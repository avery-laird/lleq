//
// Created by avery on 27/06/23.
//

#include "llvm/IR/Operator.h"
#include "llvm/Analysis/REVPass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopNestAnalysis.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Support/YAMLTraits.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Argument.h"
#include "llvm/Support/Debug.h"
#include "llvm/Analysis/Delinearization.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/DDG.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Analysis/IVDescriptors.h"
#include "llvm/Analysis/DemandedBits.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Support/Casting.h"
//#include <ostream>
#include <queue>

#define DEBUG_TYPE "revpass"

using namespace llvm;
using namespace PatternMatch;
using llvm::yaml::Output;
using llvm::yaml::MappingTraits;
using llvm::yaml::IO;

static cl::opt<std::string> AnalysisOutputPath(
    "revpass-output", cl::Hidden,
    cl::desc("The output path for revpass."));

static void GetLiveOuts(Loop *L, SmallPtrSet<Value *, 4> &LiveOuts) {
  SmallPtrSet<Value *, 5> BasePtrs;
  SmallVector<BasicBlock *> ExitBlocks;
  L->getExitBlocks(ExitBlocks);
  for (auto *BB : ExitBlocks)
    for (auto &I : *BB)
      if (auto *PN = dyn_cast<PHINode>(&I))
        LiveOuts.insert(&I);
  // TODO: considering the StoreInst
  for (auto *BB : L->getBlocks())
    for (auto &I : *BB) {
      if (isa<StoreInst>(&I)) {
        // get the GEP
        if (auto *GEP = dyn_cast<GEPOperator>(getLoadStorePointerOperand(&I))) {
          if (BasePtrs.count(GEP->getPointerOperand()))
            continue;
          LiveOuts.insert(&I); // TODO replace everything with GEPs
          BasePtrs.insert(GEP->getPointerOperand());
        }
      }
    }
}


//void denseLocateFunctions() {
//
//}

std::string getNameOrAsOperand(Value *V) {
  //  if (!V->getName().empty())
  //    return std::string(V->getName());
  std::string BBName;
  raw_string_ostream OS(BBName);
  V->printAsOperand(OS, false);
  return OS.str();
}

std::string Type2String(Type *T) {
  if (T->getTypeID() == Type::IntegerTyID)
    return "int";
  if (T->getTypeID() == Type::DoubleTyID)
    return "double";
  llvm_unreachable("unknown type.");
}

std::string Val2Sexp(Value *V, std::string Sfx = "") {
  auto T = Type2String(V->getType());
  return "(" + T + " " + getNameOrAsOperand(V) + Sfx + ")";
}

// TODO use templating
class Tensor {
public:
  enum StorageKind {
    CONTIGUOUS, CSR, CSC
  };
  Tensor(std::vector<Value *> Shape, Value *Root, Type *T, StorageKind Kind)
      : Shape(Shape), Root(Root), ElemType(T), Kind(Kind) {
    // row-major by default
    for (size_t i = 0; i < Shape.size(); ++i)
      DimOrder.push_back(i);
  }
  std::vector<Value *> Shape;
  Value *Root;
  Type *ElemType;
  const StorageKind Kind;
  std::vector<unsigned> DimOrder;

  StorageKind getKind() const { return Kind; }

  std::string toString() {
    std::string Comp = (Kind == CSR || Kind == CSC) ? "sparse " : "dense ";
    std::string TType = Type2String(ElemType) + " ";
    std::string Str = "(tensor " + Comp + TType + getNameOrAsOperand(Root) + ".Dense ";
    for (auto It = Shape.begin(); It != Shape.end(); ++It) {
      Str += "(int " + getNameOrAsOperand(*It) + ")";
      if (It != Shape.end()-1)
        Str += " ";
    }
    Str += ")";
    return Str;
  }

  std::string toStringSparse() {
    std::string Str = "(tensor dense " + Type2String(ElemType);
    Str += " " + getNameOrAsOperand(Root);
  }
};

class Executor : public InstVisitor<Executor, std::string> {
public:
//  Loop *L;
//  Executor(Loop *L) : L(L) {}

  std::string visitLoadInst(LoadInst &I) {
    // try to construct tensors optimistically
    auto *GEP = dyn_cast<GetElementPtrInst>(I.getPointerOperand());
    assert(GEP->getNumIndices() == 1);
    std::string Ptr = visit(GEP);
    std::string Idx;
    if (auto *Index = dyn_cast<Instruction>(GEP->getOperand(1)))
      Idx = visit(Index);
    else
      Idx = getNameOrAsOperand(GEP->getOperand(1));
    auto LoadType = Type2String(I.getType());
    return "(tensor dense " + LoadType + " " + Ptr + " " + Idx + ")";
  }
  std::string visitGetElementPtrInst(GetElementPtrInst &I) {
    if (auto *Ptr = dyn_cast<Argument>(I.getPointerOperand()))
      return getNameOrAsOperand(Ptr);
    auto *Inst = dyn_cast<Instruction>(I.getPointerOperand());
    return visit(Inst);
  }
  std::string visitPHINode(PHINode &I) {
    auto PhiType = Type2String(I.getType());
    return "(" + PhiType + " " + getNameOrAsOperand(&I) + ")";
  }
  std::string visitCastInst(CastInst &I) {
    if (auto *Inst = dyn_cast<Instruction>(I.getOperand(0)))
      return visit(Inst);
    auto CastType = Type2String(I.getType());
    return "(" + CastType + " " + getNameOrAsOperand(&I) + ")";
  }

  std::string visitInstruction(Instruction &I) { return visit(I); }
};

std::string Format2String(Tensor::StorageKind F) {
  switch (F) {
  default:
    llvm_unreachable("unknown format.");
  case Tensor::StorageKind::CONTIGUOUS:
    return "Dense";
  case Tensor::StorageKind::CSR:
    return "CSR";
  case Tensor::StorageKind::CSC:
    return "CSC";
  }
}

raw_ostream& operator<<(raw_ostream& os, Tensor const& t) {
  std::string output = Format2String(t.Kind) + "(<";
  for (size_t i=0; i < t.Shape.size(); ++i) {
    if (i > 0)
      output += "x";
    if (t.Shape[i] == nullptr)
      output += "?";
    else {
      output += getNameOrAsOperand(t.Shape[i]);
      //        std::string type;
      //        raw_string_ostream rs(type);
      //        t.Shape[i]->getType()->print(rs);
      //        output += type;
    }
  }
  output += ">)";
  return os << output;
}

class Vector : public Tensor {
public:
  Vector(std::vector<Value *> Shape, Type *T, Value *Root)
      : Tensor(Shape, Root, T, StorageKind::CONTIGUOUS) {}
  static bool classof(const Tensor *T) {
    return T->getKind() == StorageKind::CONTIGUOUS;
  }
};

class CSR : public Tensor {
public:
  CSR(std::vector<Value *> Shape, Type *T, Value *Root, Value *Row,
      Value *Col)
      : Tensor(Shape, Root, T, StorageKind::CSR), Row(Row), Col(Col) {}
  Value *Row = nullptr;
  Value *Col = nullptr;
  static bool classof(const Tensor *T) {
    return T->getKind() == StorageKind::CSR;
  }
};


enum LevelTypeEnum {
  COMPRESSED,
  DENSE,
  UNKNOWN
};

std::string printLevelType(LevelTypeEnum &LT) {
  switch (LT) {
  default:
    llvm_unreachable("unknown level type.");
  case COMPRESSED:
    return "COMPRESSED";
  case DENSE:
    return "DENSE";
  case UNKNOWN:
    return "UNKNOWN";
  }
}

struct LevelBounds {
  LevelTypeEnum LevelType;
  PHINode *Iterator = nullptr;
  Value *LowerBound = nullptr;
  Value *UpperBound = nullptr;
  Value *IndexExpr = nullptr;
  Value *BasePtr = nullptr;
};

bool findCrd(Value *Inst, Value **Crd) {
  std::function<bool(Value*, Value*, int, SmallPtrSet<Value*, 4>)> DFS;
  DFS = [&Crd, &DFS](Value *V, Value *PrevLoad, int Loads, SmallPtrSet<Value*, 4> Visited) {
    Visited.insert(V);
    for (auto *U : V->users()) {
      if (!Visited.contains(U)) {
        if (auto *L = dyn_cast<LoadInst>(V)) {
          if (Loads == 1) {
            *Crd = PrevLoad;
            return true;
          } else {
            PrevLoad = L;
            Loads += 1;
          }
        }
        if (DFS(U, PrevLoad, Loads, Visited))
          return true;
      }
    }
    return false;
  };
  return DFS(Inst, nullptr, 0, {});
}

//bool findCrd(Value *Inst, Value **Crd) {
//  std::vector<Value*> Stack;
//  SmallPtrSet<Value*, 4> Visited;
//  Stack.push_back(Inst);
//  int LoadCount = 0;
//  Value *PrevLoad = nullptr;
//  while (!Stack.empty()) {
//    auto *ToVisit = Stack.back();
//    Stack.pop_back();
//    if (!Visited.contains(ToVisit)) {
//      Visited.insert(ToVisit);
//      if (auto *Load = dyn_cast<LoadInst>(ToVisit)) {
//        if (LoadCount++ == 1) {
////          auto *GEP = dyn_cast<GEPOperator>(getPointerOperand(PrevLoad));
////          if (GEP == nullptr)
////            return false;
////          *Crd = GEP->getPointerOperand();
//          *Crd = PrevLoad;
//          return true;
//        } else {
//          PrevLoad = Load;
//        }
//      }
//      for (auto *Use : ToVisit->users()) {
//        if (auto *I = dyn_cast<Instruction>(Use))
//          Stack.push_back(I);
//      }
//    }
//  }
//  return false;
//}

void makeLevelBounds(LoopNest *LN, ScalarEvolution *SE, std::vector<LevelBounds> &Levels) {
  DataLayout DL = SE->getDataLayout();
//  PHINode *PrevLevel = nullptr;
  for (auto *Loop : LN->getLoops()) {
    auto Bounds = Loop->getBounds(*SE);
    if (!Bounds.has_value())
      continue;
    auto *IndVar = Loop->getInductionVariable(*SE);
    LLVM_DEBUG(dbgs() << getNameOrAsOperand(IndVar) << " = [" << Bounds->getInitialIVValue() << ", " << Bounds->getFinalIVValue() << ") -> \n");

//    std::vector<Value*> Uses;
//    followUses(IndVar, Uses);
//    for (auto *V : Uses) {
//      LLVM_DEBUG(dbgs() << *V << "\n");
//    }

    Value *LowerBound = &Bounds->getInitialIVValue();
    Value *UpperBound = &Bounds->getFinalIVValue();

    bool IsZero = match(LowerBound, m_ZeroInt());
//    bool IsInt = isa<ConstantInt>(UpperBound) || isa<Argument>(UpperBound);
    // TODO handle loads better (make sure that bounds are invariant)
    bool IsInt = UpperBound->getType()->getTypeID() == IntegerType::IntegerTyID;
    if (IsZero && IsInt) {
      LLVM_DEBUG(dbgs() << "dense\n");
      Levels.push_back({DENSE, IndVar, LowerBound, UpperBound});
//      PrevLevel = IndVar;
      continue ;
    }

    // Detect Compressed Form: pos[i] ==> pos[i+1]
    LoadInst *LowInstr = dyn_cast<LoadInst>(LowerBound);
    LoadInst *UpInstr = dyn_cast<LoadInst>(UpperBound);
    if (LowInstr && UpInstr) {
      Value *LowPtr = getLoadStorePointerOperand(LowInstr);
      Value *UpPtr = getLoadStorePointerOperand(UpInstr);
      auto *LowGEP = dyn_cast<GetElementPtrInst>(LowPtr);
      auto *HighGEP = dyn_cast<GetElementPtrInst>(UpPtr);
      if (LowGEP && HighGEP) {
        Value *LowPtrBase = LowGEP->getPointerOperand();
        Value *HighPtrBase = HighGEP->getPointerOperand();
        const SCEV *LowIndex = SE->getSCEV(LowGEP->getOperand(1));
        Value *IndexExpr = LowGEP->getOperand(1);
        while (auto *PCast = dyn_cast<CastInst>(IndexExpr))
          IndexExpr = PCast->getOperand(0);
        const SCEV *HighIndex = SE->getSCEV(HighGEP->getOperand(1));
        const SCEV *OffsetIndex = SE->getMinusSCEV(HighIndex, LowIndex);
        while (auto *PCast = dyn_cast<CastInst>(LowPtrBase))
          LowPtrBase = PCast->getOperand(0);
        while (auto *PCast = dyn_cast<CastInst>(HighPtrBase))
          HighPtrBase = PCast->getOperand(0);
        bool SameBase = LowPtrBase == HighPtrBase;
        bool OneOffset = OffsetIndex->isOne();
//        bool UsesAncestor = PrevLevel == IndexExpr;
        if (SameBase && OneOffset) {
          LLVM_DEBUG(dbgs() << "sparse\n");
          Levels.push_back({COMPRESSED, IndVar, LowerBound, UpperBound, IndexExpr, LowPtrBase});
//          PrevLevel = IndVar;
          continue;
        }
      }
    }
  }
}

struct CSRLevels {
  LevelBounds I;
  LevelBounds J;
  Value *Pos = nullptr;
  Value *Crd = nullptr;
  Value *Val = nullptr;
};


static void GetLiveIns(Function *F, SmallPtrSet<Value *, 4> &LiveIns) {
  for (auto &A : F->args())
    LiveIns.insert(&A);
  return;
}


struct Atom {
  std::string Name;
  std::string Type;
  std::string Pred;
};

std::string Type2String(Value *V) {
  std::string TypeOutput;
  raw_string_ostream TypeOutputStream(TypeOutput);
  V->getType()->print(TypeOutputStream);
  return TypeOutput;
}

struct Node {
  std::string Op;
  std::string Register;
  std::string Type;
  std::vector<Atom> Children;
public:
  Node(Instruction *I) {
    Op = I->getOpcodeName();
    if (auto *ICmp = dyn_cast<ICmpInst>(I)) {
      std::string Pred =
          CmpInst::getPredicateName(ICmp->getPredicate()).str();
      Children.push_back({Pred, "conditioncode"});
    }
    Register = getNameOrAsOperand(I);
    Type = Type2String(I);
    auto *Phi = dyn_cast<PHINode>(I);
    for (auto &C : I->operands()) {
      std::string TypeOutput = Type2String(C);
      std::string Pred = "";
      if (Phi)
        Pred = getNameOrAsOperand(Phi->getIncomingBlock(C));
      Children.push_back({getNameOrAsOperand(C), TypeOutput, Pred});
    }
  }
};

struct BBNode {
  std::string Name;
  std::vector<Node> Nodes;
};

namespace llvm::yaml {

template <> struct MappingTraits<Instruction*> {
  static void mapping(IO &io, Instruction *&I) {
    EmptyContext Ctx;
    yamlize(io, I, false, Ctx);
//    io.mapRequired("op", I->getOpcodeName());
  }
};

template <>
struct SequenceTraits<std::vector<Atom>> {
  static size_t size(IO &io, std::vector<Atom> &list) {
    return list.size();
  }
  static Atom &element(IO &io, std::vector<Atom> &list, size_t index) {
    return list[index];
  }
};

template <>
struct SequenceTraits<std::vector<::Node>> {
  static size_t size(IO &io, std::vector<::Node> &list) {
    return list.size();
  }
  static ::Node &element(IO &io, std::vector<::Node> &list, size_t index) {
    return list[index];
  }
};

template <>
struct SequenceTraits<std::vector<BBNode>> {
  static size_t size(IO &io, std::vector<BBNode> &list) {
    return list.size();
  }
  static BBNode &element(IO &io, std::vector<BBNode> &list, size_t index) {
    return list[index];
  }
};

template <> struct MappingTraits<Atom> {
  static void mapping(IO &io, Atom &A) {
    io.mapRequired("type", A.Type);
    io.mapRequired("name", A.Name);
    if (A.Pred != "")
      io.mapRequired("pred", A.Pred);
  }
};

template <> struct MappingTraits<::Node> {
  static void mapping(IO &io, ::Node &N) {
    io.mapRequired("name", N.Register);
    io.mapRequired("op", N.Op);
    io.mapRequired("type", N.Type);
    io.mapRequired("operands", N.Children);
  }
};

template <> struct MappingTraits<BBNode> {
  static void mapping(IO &io, BBNode &BN) {
    io.mapRequired("name", BN.Name);
    io.mapRequired("nodes", BN.Nodes);
  }
};

template <> struct MappingTraits<Tensor*> {
  static void mapping(IO &io, Tensor* &T) {
    std::string RootName = getNameOrAsOperand(T->Root);
    std::string Format = Format2String(T->Kind);
    io.mapRequired("root", RootName);
    io.mapRequired("format", Format);
    if (auto *CSRTensor = dyn_cast<CSR>(T)) {
      std::string Row = getNameOrAsOperand(CSRTensor->Row);
      std::string Col = getNameOrAsOperand(CSRTensor->Col);
      io.mapRequired("row", Row);
      io.mapRequired("col", Col);
    } else if (auto *V = dyn_cast<Vector>(T)) {
      // do nothing
    } else {
      llvm_unreachable("unknown format.");
    }
  }
};
template <>
struct SequenceTraits<std::vector<Tensor*>> {
  static size_t size(IO &io, std::vector<Tensor*> &list) {
    return list.size();
  }
  static Tensor* &element(IO &io, std::vector<Tensor*> &list, size_t index) {
    return list[index];
  }
};

//template <> struct MappingTraits<LevelBounds> {
//  static void mapping(IO &io, LevelBounds &LB) {
//    std::string IndVar = getNameOrAsOperand(LB.Iterator);
//    std::string LevelType = printLevelType(LB.LevelType);
//    io.mapRequired("indvar", LB.);
//    io.mapRequired("nodes", BN.Nodes);
//  }
//};
} // namespace llvm::yaml


void allLoadsInCurrentScope(Loop *L, SmallPtrSet<LoadInst*, 4> &Loads) {
  for (auto *BB : L->blocks()) {
    for (auto &I : *BB) {
      if (auto *Load = dyn_cast<LoadInst>(&I)) {
        Loads.insert(Load);
      }
    }
  }
}

std::string buildExpression(Value *LiveOut, PHINode *Iterator, RecurrenceDescriptor &RD, DenseMap<Value*, LevelBounds> &LevelMap, DenseMap<Value*, Tensor*> &TensorMap) {
  if (RD.getRecurrenceKind() == RecurKind::FMulAdd) {
    auto *I = dyn_cast<Instruction>(LiveOut);
    Executor E;
    std::string Astr = E.visit(cast<Instruction>(I->getOperand(0)));
    std::string Bstr = E.visit(cast<Instruction>(I->getOperand(1)));
    return "(+ (* " + Astr + " " + Bstr + "))";
  } else {
    llvm_unreachable("unknown recurrence kind.");
  }
}

std::string buildDenseExpression(Value *LiveOut, PHINode *Iterator, RecurrenceDescriptor &RD, DenseMap<Value*, LevelBounds> &LevelMap, DenseMap<Value*, Tensor*> &TensorMap) {
  if (RD.getRecurrenceKind() == RecurKind::FMulAdd) {
    auto *I = dyn_cast<Instruction>(LiveOut);
    Tensor *A = TensorMap[I->getOperand(0)];
    Tensor *B = TensorMap[I->getOperand(1)];
    std::string Astr = A->toString();
    std::string Bstr = B->toString();
    return "(+ (* " + Astr + " " + Bstr + "))";
  } else {
    llvm_unreachable("unknown recurrence kind.");
  }
}

void emitFold(Value *LiveOut, PHINode *Iterator,
              RecurrenceDescriptor &RD,
              DenseMap<Value *, LevelBounds> &LevelMap,
              DenseMap<Value *, Tensor *> &TensorMap) {
//  Value *Init;
  std::string Expr = "(fold ";
  std::string End;
  auto *StartVal = RD.getRecurrenceStartValue().getValPtr();
  LevelBounds &Bounds = LevelMap[Iterator];
  auto *LowerBound = Bounds.LowerBound;
  auto *IndVar = Iterator;
  auto *UpperBound = Bounds.UpperBound;
  Expr += Val2Sexp(StartVal) + " ";
  Expr += Val2Sexp(LowerBound) + " ";
  Expr += Val2Sexp(IndVar) + " ";
  Expr += Val2Sexp(UpperBound) + " ";
  Expr += buildExpression(LiveOut, Iterator, RD, LevelMap, TensorMap);
  Expr += ")";
  LLVM_DEBUG({
    dbgs() << Expr << "\n";
  });
  // now the dense version
  std::string DenseExpr = "(fold ";
  std::string DenseLowerBound, DenseUpperBound;
  if (LevelMap[Iterator].LevelType == COMPRESSED) {
    DenseLowerBound = "(int 0)";
    DenseUpperBound = "(int " + getNameOrAsOperand(Iterator) + ".end)";
  } else {
    DenseLowerBound = "(int " + getNameOrAsOperand(LevelMap[Iterator].LowerBound) + ")";
    DenseUpperBound = "(int " + getNameOrAsOperand(LevelMap[Iterator].UpperBound) + ")";
  }
  DenseExpr += Val2Sexp(StartVal) + " ";
  DenseExpr += DenseLowerBound + " ";
  DenseExpr += Val2Sexp(IndVar) + " ";
  DenseExpr += DenseUpperBound + " ";
  DenseExpr += buildDenseExpression(LiveOut, Iterator, RD, LevelMap, TensorMap);
  DenseExpr += ")";
  LLVM_DEBUG({
    dbgs() << DenseExpr << "\n";
  });
}

void emitMap(Value *LiveOut, PHINode *Iterator,
             RecurrenceDescriptor &RD,
             DenseMap<Value *, LevelBounds> &LevelMap,
             DenseMap<Value *, Tensor *> &TensorMap) {
  Value *Init;
  std::string End;
  if (LevelMap[Iterator].LevelType == COMPRESSED)
    End = getNameOrAsOperand(Iterator) + ".end";
  else
    End = getNameOrAsOperand(LevelMap[Iterator].UpperBound);
  LLVM_DEBUG({
     dbgs() << "map 0 " << End << "\n";
  });
}

enum Property {
  FULL, ORDERED, UNIQUE, BRANCHLESS, COMPACT
};

void findFirstDep(Value *Operand, SmallPtrSetImpl<Value*> &Inputs) {
  std::queue<Value*> Queue;
  SmallPtrSet<Value*, 5> Visited;
  Queue.push(Operand);
  while (!Queue.empty()) {
    auto *ToVisit = Queue.front();
    Queue.pop();
    if (isa<LoadInst>(ToVisit) /*|| isa<PHINode>(ToVisit)*/) {
      Inputs.insert(ToVisit);
      continue;
    }
    if (auto *I = dyn_cast<Instruction>(ToVisit)) {
      for (auto &Op : I->operands()) {
        if (!Visited.contains(Op)) {
          Visited.insert(Op);
          Queue.push(Op);
        }
      }
    }
  }
  return;
}

// CSR val tree:

Value *skipCasts(Value *V) {
  while (auto *Cast = dyn_cast<CastInst>(V))
    V = Cast->getOperand(0);
  return V;
}

bool detectCSC(LoopInfo *LI, Value *Root, Value **Row, Value **Col, Value **Val, DenseMap<Value*, LevelBounds> &LevelMap) {
  // Row is optional
  Instruction *I, *J;
  *Row = *Col = *Val = I = J = nullptr;
  // match 1st gep
  Value *Next = nullptr;
  if (auto *Load = dyn_cast<LoadInst>(Root))
    Next = skipCasts(Load->getPointerOperand());
  else
    return false;

  if (auto *GEP = dyn_cast<GEPOperator>(Next)) {
    if (GEP->getNumIndices() != 1)
      return false;
    *Val = GEP->getPointerOperand();
    Next = skipCasts(GEP->getOperand(1));
  } else {
    return false;
  }

  if (LevelMap.contains(Next) && LevelMap[Next].LevelType == COMPRESSED) {
    J = dyn_cast<Instruction>(Next);
    auto *Phi = dyn_cast<PHINode>(Next);
    if (!Phi)
      return false;
    // unique incoming/non-backedge
    int NonBackedge = 0;
    for (size_t i = 0; i < Phi->getNumIncomingValues(); ++i) {
      if (LI->getLoopFor(Phi->getParent())->contains(Phi->getIncomingBlock(i)))
        continue;
      else {
        NonBackedge++;
        if (NonBackedge > 1)
          return false;
        Next = skipCasts(Phi->getIncomingValue(i));
      }
    }
  } else {
    return false;
  }

  if (auto *Load = dyn_cast<LoadInst>(Next))
    Next = skipCasts(Load->getPointerOperand());
  else
    return false;

  if (auto *GEP = dyn_cast<GEPOperator>(Next)) {
    if (GEP->getNumIndices() != 1)
      return false;
    *Row = GEP->getPointerOperand();
    Next = skipCasts(GEP->getOperand(1));
  } else {
    return false;
  }

  if (LevelMap.contains(Next) && LevelMap[Next].LevelType == DENSE) {
    I = dyn_cast<Instruction>(Next);
  } else {
    return false;
  }

  // try for Col also
  if (findCrd(J, Col)) {
    auto JBounds = LevelMap[J];
    JBounds.LevelType = DENSE;
    LevelMap[*Col] = JBounds;
  }
  return true;
}

bool detectCSR(LoopInfo *LI, Value *Root, Value **Row, Value **Col, Value **Val, Value **I, Value**J, DenseMap<Value*, LevelBounds> &LevelMap) {
  // Col is optional
//  Instruction *I, *J;
  *Row = *Col = *Val = *I = *J = nullptr;
  // match 1st gep
  Value *Next = nullptr;
  if (auto *Load = dyn_cast<LoadInst>(Root))
    Next = skipCasts(Load->getPointerOperand());
  else
    return false;

  if (auto *GEP = dyn_cast<GEPOperator>(Next)) {
    if (GEP->getNumIndices() != 1)
      return false;
    *Val = GEP->getPointerOperand();
    Next = skipCasts(GEP->getOperand(1));
  } else {
    return false;
  }

  if (LevelMap.contains(Next) && LevelMap[Next].LevelType == COMPRESSED) {
    *J = dyn_cast<Instruction>(Next);
    auto *Phi = dyn_cast<PHINode>(Next);
    if (!Phi)
      return false;
    // unique incoming/non-backedge
    int NonBackedge = 0;
    for (size_t i = 0; i < Phi->getNumIncomingValues(); ++i) {
      if (LI->getLoopFor(Phi->getParent())->contains(Phi->getIncomingBlock(i)))
        continue;
      else {
        NonBackedge++;
        if (NonBackedge > 1)
          return false;
        Next = skipCasts(Phi->getIncomingValue(i));
      }
    }
  } else {
    return false;
  }

  if (auto *Load = dyn_cast<LoadInst>(Next))
    Next = skipCasts(Load->getPointerOperand());
  else
    return false;

  if (auto *GEP = dyn_cast<GEPOperator>(Next)) {
    if (GEP->getNumIndices() != 1)
      return false;
    *Row = GEP->getPointerOperand();
    Next = skipCasts(GEP->getOperand(1));
  } else {
    return false;
  }

  if (LevelMap.contains(Next) && LevelMap[Next].LevelType == DENSE) {
    *I = dyn_cast<Instruction>(Next);
//    *Rows = LevelMap[Next].UpperBound;
  } else {
    return false;
  }

  // try for Col also
  if (findCrd(*J, Col)) {
    auto JBounds = LevelMap[*J];
    JBounds.LevelType = DENSE;
    LevelMap[*Col] = JBounds;
  }
  return true;
}

bool detectDense2D(LoopInfo *LI, ScalarEvolution *SE, LoadInst *Root, Value **A, Value **Pk_1, Value **Nk, Value **Ik, DenseMap<Value*, LevelBounds> &LevelMap) {
  Instruction *I, *J;
  *A = *Pk_1 = *Nk = *Ik = nullptr;

  Value *Next = nullptr;
  if (auto *Load = dyn_cast<LoadInst>(Root))
    Next = skipCasts(Load->getPointerOperand());
  else
    return false;

  if (auto *GEP = dyn_cast<GEPOperator>(Next)) {
    if (GEP->getNumIndices() != 1)
      return false;
    *A = GEP->getPointerOperand();
    Next = skipCasts(GEP->getOperand(1));
  } else {
    return false;
  }
  // match the mul
  // TODO handle associativity
  if (auto *Add = dyn_cast<AddOperator>(Next)) {
    J = dyn_cast<Instruction>(skipCasts(Add->getOperand(1)));
    if (J == nullptr)
      return false;
    if (LevelMap.contains(J) && LevelMap[J].LevelType == DENSE) {
        *Ik = J;
    } else {
      return false;
    }
    Next = skipCasts(Add->getOperand(0));
  } else {
    return false;
  }

  if (auto *Mul = dyn_cast<MulOperator>(Next)) {
    // Nk can't ever change and should be the close level upper bound
    *Nk = skipCasts(Mul->getOperand(1));
//    if (LevelMap[J].UpperBound != *Nk)
//      return false;
    if (!LI->getLoopFor(LevelMap[J].Iterator->getParent())->isLoopInvariant(*Nk))
      return false;
    Next = skipCasts(Mul->getOperand(0));
  }

  if (LevelMap.contains(Next) && LevelMap[Next].LevelType == DENSE) {
    *Pk_1 = LevelMap[Next].Iterator;
  } else {
    return false;
  }

  return true;

//  const SCEV *AccessFn = SE->getSCEVAtScope(getPointerOperand(Root), LI->getLoopFor(Root->getParent()));
//  const SCEV *BasePointer = dyn_cast<SCEVUnknown>(SE->getPointerBase(AccessFn));
//  AccessFn = SE->getMinusSCEV(AccessFn, BasePointer);
//  auto *TryCast = dyn_cast<SCEVAddRecExpr>(AccessFn);
//  LLVM_DEBUG(dbgs() << *Root << " ==> " << *TryCast << "\n");
//  SmallVector<const SCEV*> Subscripts, Sizes;
//  delinearize(*SE, TryCast, Subscripts, Sizes, SE->getElementSize(Root));
//  LLVM_DEBUG({
//      for (auto *S : Subscripts)
//        dbgs() << *S << "\n";
//      for (auto *S : Sizes)
//        dbgs() << *S << "\n";
//  });

  return false;
}

bool detectDense1D(LoopInfo *LI, ScalarEvolution *SE, LoadInst *Root, Value **x, Value **Ik, DenseMap<Value*, LevelBounds> &LevelMap) {
  *x = *Ik = nullptr;

  Value *Next = nullptr;
  if (auto *Load = dyn_cast<LoadInst>(Root))
    Next = skipCasts(Load->getPointerOperand());
  else
    return false;

  if (auto *GEP = dyn_cast<GEPOperator>(Next)) {
    if (GEP->getNumIndices() != 1)
      return false;
    *x = GEP->getPointerOperand();
    Next = skipCasts(GEP->getOperand(1));
  } else {
    return false;
  }

  if (LevelMap.contains(Next) && LevelMap[Next].LevelType == DENSE) {
    *Ik = LevelMap[Next].Iterator;
  } else {
    return false;
  }

  return true;
}

bool coverAllLoads(LoopInfo *LI, ScalarEvolution *SE,
                   SmallVector<LoadInst *> &Loads,
                   DenseMap<Value *, LevelBounds> &LevelMap,
                   SmallPtrSetImpl<LoadInst *> &Leftover,
                   DenseMap<Value*, Tensor*> &TensorMap) {
  // 1. how the load is indexed? eg by dense or compressed level iterator
  // 2. how the load is used? eg as ptr (to index other array) or in
  // computation?
  bool Change = true;
  SmallPtrSet<LoadInst *, 5> WorkList;
  for (auto *L : Loads)
    WorkList.insert(L);
  while (Change) {
    Change = false;
    SmallVector<LoadInst *> ToRemove;
    for (auto *Load :
         WorkList) { // TODO figure out how to undo LevelMap mutations
      Value *Row, *Col, *Val, *I, *J;
      auto IsCSR = detectCSR(LI, Load, &Row, &Col, &Val, &I, &J, LevelMap);
      if (IsCSR) {
        auto *TensorCSR = new CSR({I, J}, Load->getType(), Val, Row, Col);
//        CSR TensorCSR({Rows, nullptr}, Val, Row, Col);
        TensorMap[Load] = TensorCSR;
        LLVM_DEBUG({
          dbgs() << "detected CSR:\n";
          dbgs() << "val = " << *Val << "\n";
          dbgs() << "row = " << *Row << "\n";
          if (Col)
            dbgs() << "col = " << *Col << "\n";
          dbgs() << *TensorCSR << "\n";
        });
        ToRemove.push_back(Load);
        Change = true;
        continue;
      }
      //      auto IsCSC = detectCSC(LI, Load, &Row, &Col, &Val, LevelMap);
      //      if (IsCSC) {
      //        LLVM_DEBUG({
      //          dbgs() << "detected CSC:\n";
      //          dbgs() << "val = " << *Val << "\n";
      //          dbgs() << "row = " << *Row << "\n";
      //          if (Col)
      //            dbgs() << "col = " << *Col << "\n";
      //        });
      //        ToRemove.push_back(Load);
      //        Change = true;
      //        continue;
      //      }
      Value *A, *Pk_1, *Nk, *Ik;
      auto IsDense2D =
          detectDense2D(LI, SE, Load, &A, &Pk_1, &Nk, &Ik, LevelMap);
      if (IsDense2D) {
        auto *D1 = LevelMap[Pk_1].UpperBound;
        auto *D2 = LevelMap[Ik].UpperBound;
        auto *Dense2D = new Vector({Pk_1, Ik}, Load->getType(), A);
//        Vector Dense2D({D1, D2}, A);
        TensorMap[Load] = Dense2D;
        LLVM_DEBUG({
          dbgs() << "detected dense 2d\n";
          dbgs() << "A = " << *A << "\n";
          dbgs() << "p_{k-1} = " << *Pk_1 << "\n";
          dbgs() << "N_k = " << *Nk << "\n";
          dbgs() << "i_k = " << *Ik << "\n";
          dbgs() << *Dense2D << "\n";
        });
        ToRemove.push_back(Load);
        Change = true;
        continue;
      }
      Value *x;
      auto IsDense1D = detectDense1D(LI, SE, Load, &x, &Ik, LevelMap);
      if (IsDense1D) {
        auto *D1 = LevelMap[Ik].UpperBound;
        auto *Dense1D = new Vector({Ik}, Load->getType(), x);
//        Vector Dense1D({D1}, x);
        TensorMap[Load] = Dense1D;
        LLVM_DEBUG({
          dbgs() << "detected dense 1d\n";
          dbgs() << "x = " << *x << "\n";
          dbgs() << "i_k = " << *Ik << "\n";
          dbgs() << *Dense1D << "\n";
        });
        ToRemove.push_back(Load);
        Change = true;
        continue;
      }
    }
    for (auto *L : ToRemove)
      WorkList.erase(L);
  }

  Leftover.insert(WorkList.begin(), WorkList.end());

  return WorkList.size() == 0;
  //  for (auto *Load : Loads) {
  //    Value *Row, *Col, *Val;
  //    auto IsCSR = detectCSR(LI, Load, &Row, &Col, &Val, LevelMap);
  //    if (IsCSR) {
  //      LLVM_DEBUG({
  //        dbgs() << "detected CSR:\n";
  //         dbgs() << "val = " << *Val << "\n";
  //         dbgs() << "row = " << *Row << "\n";
  //         if (Col)
  //           dbgs() << "col = " << *Col << "\n";
  //      });
  //      continue;
  //    }
  //    Value *A, *Pk_1, *Nk, *Ik;
  //    auto IsDense2D = detectDense2D(LI, SE, Load, &A, &Pk_1, &Nk, &Ik,
  //    LevelMap); if (IsDense2D) {
  //      LLVM_DEBUG({
  //          dbgs() << "detected dense 2d\n";
  //          dbgs() << "A = " << *A << "\n";
  //          dbgs() << "p_{k-1} = " << *Pk_1 << "\n";
  //          dbgs() << "N_k = " << *Nk << "\n";
  //          dbgs() << "i_k = " << *Ik << "\n";
  //      });
  //      continue;
  //    }

  //    const SCEV *AccessFn = SE->getSCEV(getPointerOperand(Load));
  //    const SCEV *BasePointer =
  //    dyn_cast<SCEVUnknown>(SE->getPointerBase(AccessFn)); AccessFn =
  //    SE->getMinusSCEV(AccessFn, BasePointer); auto *TryCast =
  //    dyn_cast<SCEVAddRecExpr>(AccessFn); bool IsAffine = TryCast != nullptr
  //    && TryCast->isAffine(); LLVM_DEBUG(dbgs() << *AccessFn << ", isAffine="
  //    << IsAffine << "\n"); if (!IsAffine) {
  //      // chase load
  //    } else {
  //      // lookup level access
  //    }
  //    if (SCEVExprContains(AccessFn, [](const SCEV *S) { return }))
  //    SmallVector<const SCEV*> Subscripts, Sizes;
  //    delinearize(*SE, AccessFn, Subscripts, Sizes, SE->getElementSize(Load));
  //    for (auto *S : Subscripts) {
  //      LLVM_DEBUG(dbgs() << *S << "\n");
  //    }
}

void makeTopLevelInputs(Value *LiveOut, SmallPtrSetImpl<Value*> &Inputs) {
  if (auto *Store = dyn_cast<StoreInst>(LiveOut))
    LiveOut = Store->getValueOperand();
  auto *Inst = dyn_cast<Instruction>(LiveOut);
  if (Inst == nullptr)
    return; // no inputs, some constant value
  // first load or scalar inputs
  for (auto &Op : Inst->operands()) {
    if (isa<IntrinsicInst>(Inst) && isa<Function>(Op))
      continue;
    findFirstDep(Op, Inputs);
//    LLVM_DEBUG(dbgs() << *Dep << "\n");
//    Inputs.push_back(Dep);
  }
}

Value *findLiveOut(Loop *L, LoopInfo *LI) {
  auto *ExitBB = L->getExitBlock();
  assert(ExitBB && "only one exit block allowed.");
  Value *MemoryLO = nullptr;
  PHINode *ScalarLO = nullptr;
  int NumPhis = 0;
  for (auto &Phi : ExitBB->phis()) {
    ScalarLO = &Phi;
    NumPhis++;
  }
  SmallVector<Value*> StoreInsts;
  for (auto *BB : L->blocks())
    for (auto &I : *BB) {
      auto *ParentLoop = LI->getLoopFor(I.getParent());
      if (ParentLoop != L)
        break;
      if (isa<StoreInst>(&I))
        StoreInsts.push_back(&I);
    }
  if (NumPhis == 0 && StoreInsts.empty())
    return nullptr;
  bool Legal = (NumPhis == 1) != (StoreInsts.size() == 1);
  assert(Legal && "only one live out allowed.");
  if (NumPhis == 1) {
    assert(ScalarLO->getNumIncomingValues() == 1 && "only one incoming value allowed.");
    return ScalarLO->getOperand(0);
  }
  return StoreInsts[0];
}

PreservedAnalyses REVPass::run(Function &F, FunctionAnalysisManager &AM) {
  outs() << F.getName() << "\n";

  LoopInfo &LI = AM.getResult<LoopAnalysis>(F);
  ScalarEvolution &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
  DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
//  DDGAnalysis::Result &DDG = AM.getResult<DDGAnalysis>(F);

  Node *LO;
  std::vector<LevelBounds> Levels;
  struct CSRLevels CSR;
  if (LI.getTopLevelLoops().size() == 0) {
    // TODO handle memory too
    for (auto &BB: F) {
      for (auto &I : BB) {
        if (auto *Ret = dyn_cast<ReturnInst>(&I)) {
          LO = new Node(Ret);
          break; // TODO multiple values
        }
      }
    }
  } else {
    LoopNest LN(*LI.getTopLevelLoops()[0], SE);
    makeLevelBounds(&LN, &SE, Levels);
    DenseMap<Value *, LevelBounds> LevelMap;
    for (auto &Level : Levels)
      LevelMap[Level.Iterator] = Level;

    // get all liveouts
    DenseMap<Loop *, Value *> LiveOutMap;

    DenseMap<Loop *, SmallPtrSet<Value *, 5>> Loop2Loads;
    for (auto *Loop : LN.getLoops()) {
      // collect live out (store or scalar live-out)
      Value *LiveOut = findLiveOut(Loop, &LI);
      if (LiveOut == nullptr) {
        LLVM_DEBUG(dbgs() << "no liveouts.\n");
        continue;
      }
      LLVM_DEBUG(dbgs() << "live out = " << *LiveOut << "\n");
      LiveOutMap[Loop] = LiveOut;
      SmallPtrSet<Value *, 5> TopLevelInputs;
      makeTopLevelInputs(LiveOut, TopLevelInputs);
      Loop2Loads[Loop] = TopLevelInputs;
    }

    SmallVector<LoadInst *> TopLevelLoads;
    for (auto &E : Loop2Loads) {
      for (auto *Input : E.second)
        if (auto *Load = dyn_cast<LoadInst>(Input))
          TopLevelLoads.push_back(Load);
    }

    LLVM_DEBUG({
      dbgs() << "Top level loads ------------\n";
      for (auto *In : TopLevelLoads)
        dbgs() << *In << "\n";
      dbgs() << "----------------------------\n";
    });

    SmallPtrSet<LoadInst *, 5> Leftover;
    DenseMap<Value *, Tensor*> TensorMap;
    auto AllCovered =
        coverAllLoads(&LI, &SE, TopLevelLoads, LevelMap, Leftover, TensorMap);
    LLVM_DEBUG({
      if (AllCovered)
        dbgs() << "all loads covered.\n";
      else {
        dbgs() << "remaining loads:\n";
        for (auto *L : Leftover)
          dbgs() << *L << "\n";
      }
    });

    AssumptionCache AC(F);
    DemandedBits DB(F, AC, DT);

    for (int Depth = LN.getNestDepth(); Depth > 0; Depth--) {
      for (auto *Loop : LN.getLoopsAtDepth(Depth)) {
        // get liveout for loop
        Value *LiveOut = LiveOutMap[Loop];
        if (LiveOut == nullptr)
          continue;

        RecurrenceDescriptor RD;
        if (any_of(Loop->getHeader()->phis(), [&](PHINode &Phi) {
              return RecurrenceDescriptor::isReductionPHI(&Phi, Loop, RD, &DB,
                                                          &AC, &DT, &SE) &&
                     RD.getLoopExitInstr() == LiveOut;
            })) {
          LLVM_DEBUG(dbgs() << *LiveOut << " is a reduction.\n");
          // candidate for fold
          emitFold(LiveOut, Loop->getInductionVariable(SE), RD, LevelMap, TensorMap);
          continue;
        }
        // is it a reduction?
//        for (auto &Phi : Loop->getHeader()->phis()) {
//          RecurrenceDescriptor RD;
//          if (!RecurrenceDescriptor::isReductionPHI(&Phi, Loop, RD, &DB, &AC, &DT, &SE))
//            continue;
//          // see if it's the liveout
//          if (RD.getLoopExitInstr() == LiveOut) {
//            LLVM_DEBUG(dbgs() << *LiveOut << " is a reduction.\n");
//            // candidate for fold
//            emitFold(LiveOut, Loop->getInductionVariable(SE), LevelMap);
//            continue;
//          }
//        }
        // is it a map?
        if (auto *Store = dyn_cast<StoreInst>(LiveOut)) {
          emitMap(LiveOut, Loop->getInductionVariable(SE), RD, LevelMap, TensorMap);
        }

      }
    }

    //    for (int Depth = LN.getNestDepth(); Depth > 0; Depth--) {
    //      for (auto *Loop : LN.getLoopsAtDepth(Depth)) {
    //        LLVM_DEBUG(dbgs() << "-----------------------\n");
    //        LLVM_DEBUG(dbgs() << "Loop at depth " << Depth << ":\n");
    //        // collect all inputs (loads only) in the current scope
    //        SmallPtrSet<LoadInst*, 4> Loads;
    //        allLoadsInCurrentScope(Loop, Loads);
    //
    //        // collect live out (store or scalar live-out)
    //        Value *LiveOut = findLiveOut(Loop, &LI);
    //        if (LiveOut == nullptr) {
    //          LLVM_DEBUG(dbgs() << "no liveouts.\n");
    //          continue;
    //        }
    //        LLVM_DEBUG(dbgs() << "live out = " << *LiveOut << "\n");
    //
    //        // make top-level dependences (value arrays + scalar inputs)
    //        SmallVector<Value*> TopLevelInputs;
    //        LLVM_DEBUG(dbgs() << "Inputs ------------\n");
    //        makeTopLevelInputs(LiveOut, TopLevelInputs);
    //        LLVM_DEBUG(dbgs() << "-------------------\n");
    //        SmallVector<LoadInst*> InputLoads;
    //        for (auto *V : TopLevelInputs)
    //          if (auto *Load = dyn_cast<LoadInst>(V))
    //            InputLoads.push_back(Load);
    //
    ////        for (auto *Load : Loads)
    ////          LLVM_DEBUG(dbgs() << *Load << "\n");
    //        coverAllLoads(&LI, Loop, &SE, InputLoads, LevelMap);
    //        LLVM_DEBUG(dbgs() << "-----------------------\n");
    //      }
    //    }

    //    bool IsCSR = detectCSR(Levels, &CSR);
    //    LLVM_DEBUG(dbgs() << "iscsr = " << IsCSR << "\n");

    SmallPtrSet<Value *, 4> LiveOuts;
    GetLiveOuts(&LN.getOutermostLoop(), LiveOuts);

    Instruction *LiveOut = dyn_cast<Instruction>(*LiveOuts.begin());
    LO = new Node(LiveOut);

    std::error_code EC;
    raw_fd_ostream OutputFile(AnalysisOutputPath + ".yaml", EC);
    Output Yout(OutputFile);

    SmallPtrSet<Value *, 4> LiveIns;
    GetLiveIns(&F, LiveIns);
    std::vector<Atom> LiveInList;
    for (auto *LiveIn : LiveIns)
      LiveInList.push_back(
          {getNameOrAsOperand(LiveIn), Type2String(LiveIn), ""});

    //  std::vector<Value *> WorkList;
    //  WorkList.insert(WorkList.begin(), LiveIns.begin(), LiveIns.end());
    //  SmallPtrSet<Value *, 4> Dense;
    //  while(!WorkList.empty()) {
    //    Value *Head = WorkList.back();
    //    if (Head == CSR.I.UpperBound ||
    //        Head == CSR.Crd ||
    //        Head == CSR.Pos) {
    //      WorkList.pop_back();
    //    }
    //  }

    std::vector<Tensor*> AllTensors;
    for (auto &E : TensorMap)
      AllTensors.push_back(E.second);

    std::vector<BBNode> AllBBs;
    for (auto &BB : F) {
      BBNode BN;
      BN.Name = BB.getName();
      for (auto &I : BB) {
        BN.Nodes.push_back(Node(&I));
      }
      AllBBs.push_back(BN);
    }
    Yout << AllBBs;
    Yout << *LO;
    Yout << LiveInList;
    Yout << AllTensors;

    for (auto &E : TensorMap) {
      delete E.second; // TODO use smart pointers
    }
  }
  return PreservedAnalyses::all();
}