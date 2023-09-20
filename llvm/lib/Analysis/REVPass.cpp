//
// Created by avery on 27/06/23.
//

#include "llvm/ADT/SCCIterator.h"
#include "llvm/Analysis/REVPass.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/DDG.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/Delinearization.h"
#include "llvm/Analysis/DemandedBits.h"
#include "llvm/Analysis/IVDescriptors.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopNestAnalysis.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/YAMLTraits.h"
// #include <ostream>
#include <queue>

#define DEBUG_TYPE "revpass"

using namespace llvm;
using namespace PatternMatch;
using llvm::yaml::IO;
using llvm::yaml::MappingTraits;
using llvm::yaml::Output;


void makeTopLevelInputs(Value *LiveOut, SmallPtrSetImpl<Value *> &Inputs);

static cl::opt<std::string>
    AnalysisOutputPath("revpass-output", cl::Hidden,
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

// void denseLocateFunctions() {
//
// }

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
  if (T->getTypeID() == Type::FloatTyID)
    return "double"; // TODO treat everything as float
  llvm_unreachable("unknown type.");
}

std::string Val2Sexp(Value *V, std::string Sfx = "") {
  auto T = Type2String(V->getType());
  return "(" + T + " " + getNameOrAsOperand(V) + Sfx + ")";
}

// TODO use templating
class Tensor {
public:
  enum StorageKind { CONTIGUOUS, CSR, CSC };
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
    std::string Str =
        "(tensor " + Comp + TType + getNameOrAsOperand(Root);
    if (Comp == "sparse ")
      Str += ".Dense";
    Str += " ";
    for (auto It = Shape.begin(); It != Shape.end(); ++It) {
      Str += "(int " + getNameOrAsOperand(*It) + ")";
      if (It != Shape.end() - 1)
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


class Exp {
public:
  virtual void print(raw_ostream &OS) const = 0;
  void dump() { print(dbgs()); }
};
raw_ostream &operator<<(raw_ostream &OS, Exp const &E) {
  E.print(OS);
  return OS;
}

class Var : public Exp {
  std::vector<Value*> Elems;
public:
  Var(Value* V) { Elems.push_back(V); }
  Var(std::vector<Value*> &Elems) : Elems(Elems) {}
  Var(iterator_range<Function::arg_iterator> Args) {
    for (auto &A : Args)
      Elems.push_back(&A);
  }
  void print(raw_ostream &OS) const {
    OS << "(";
    ListSeparator LS(", ");
    for (auto *V : Elems)
      OS << LS << getNameOrAsOperand(V);
    OS << ")";
  }
};
class Abs : public Exp {
  Var *Params = nullptr;
  Exp *Body = nullptr;
public:
  Abs(Var *P, Exp *B) : Params(P), Body(B) {}
};
class Apply : public Exp {};
class Builtin : public Exp {
  Instruction *InstOp;
  std::vector<Exp *> Es;

  void makeOp() {
    switch (InstOp->getOpcode()) {
    default:
      llvm_unreachable("unsupported builtin.");
    case Instruction::ICmp:
      auto Pred = dyn_cast<CmpInst>(InstOp)->getPredicate();
      if (Pred == CmpInst::Predicate::ICMP_SGT)
        Op = GT;
      else
        llvm_unreachable("unsupported ICmp predicate.");
    }
  }
  std::string op2String() const {
    switch (Op) {
    case Add:
      return "+";
    case Mult:
      return "*";
    case LT:
      return "<";
    case GT:
      return ">";
    case Not:
      return "not";
    }
  }
public:
  enum SupportedOps {
    Add, Mult, LT, GT, Not
  };
  SupportedOps Op;

  Builtin(Instruction *Op, Exp *L, Exp *R) : InstOp(Op), Es({L, R}) {
    makeOp();
  }
  Builtin(SupportedOps Op, Exp *E) : Op(Op), Es({E}) {}
  static Builtin *mkNot(Exp *E) {
    return new Builtin(Not, E);
  }
  void print(raw_ostream &OS) const {
    OS << "("  << op2String() << " ";
    ListSeparator LS(" ");
    for (auto *Operand : Es) {
      OS << LS;
      Operand->print(OS);
    }
    OS << ")";
  }


};

class IfThen : public Exp {
  Exp *C;
  Exp *Then;
  Exp *Else;
public:
  IfThen(Exp *C, Exp *T, Exp *E) : C(C), Then(T), Else(E) {}
  void print(raw_ostream &OS) const {
    OS << "if " << *C << " then " << *Then << " else " << *Else;
  }
};
class Let : public Exp {
  Var *L;
  Exp *V;
  Exp *B;
public:
  Let(Var *L, Exp *V, Exp *B) : L(L), V(V), B(B) {}
  void print(raw_ostream &OS) const {
    OS << "let " << *L << " = " << *V << " in " << *B << "\n";
  }
};
class Tuple : public Exp {};
class MemLoad : public Exp {
  Exp *Ptr;
  Exp *Idx;
  LoadInst *L = nullptr;
public:
  MemLoad(Exp *Ptr, Exp *Idx, LoadInst *L) : Ptr(Ptr), Idx(Idx), L(L) {}
  void print(raw_ostream &OS) const {
    OS << *Ptr << "[" << *Idx << "]";
  }
};
class MemStore : public Exp {};

// inline everything except for loads
class Inline : public InstVisitor<Inline, Exp*> {
public:
//  Inline(raw_ostream &OS) : OS(OS) {}

  Exp *run(Value *V) {
    if (auto *I = dyn_cast<Instruction>(V))
      return visit(I);
    return new Var(V);
  }

  Exp *visitLoadInst(LoadInst &I) {
    // try to construct tensors optimistically
    auto *GEP = dyn_cast<GetElementPtrInst>(I.getPointerOperand());
    assert(GEP->getNumIndices() == 1);
    auto Ptr = visit(GEP);
    Exp *Idx;
    if (auto *Index = dyn_cast<Instruction>(GEP->getOperand(1)))
      Idx = visit(Index);
    else
      Idx = new Var(GEP->getOperand(1));
    return new MemLoad(Ptr, Idx, &I);
  }

  Exp *visitGetElementPtrInst(GetElementPtrInst &I) {
    if (auto *Ptr = dyn_cast<Argument>(I.getPointerOperand()))
      return new Var(Ptr);
    auto *Inst = dyn_cast<Instruction>(I.getPointerOperand());
    return visit(Inst);
  }

  Exp *visitCastInst(CastInst &I) { return run(I.getOperand(0)); }

  Exp *visitBinOrCmp(Instruction &I) {
    auto Left = run(I.getOperand(0));
    auto Right = run(I.getOperand(1));
    return new Builtin(&I, Left, Right);
  }

  Exp *visitBinaryOperator(BinaryOperator &I) { return visitBinOrCmp(I); }

  Exp *visitCmpInst(CmpInst &I) { return visitBinOrCmp(I); }

  Exp *visitInstruction(Instruction &I) { return visit(I); }

private:
//  raw_ostream &OS;
};

class Executor : public InstVisitor<Executor, std::string> {
public:
  //  Loop *L;
  //  Executor(Loop *L) : L(L) {}

  std::string SExpr(Value *V) {
    if (auto *I = dyn_cast<Instruction>(V))
      return visit(I);
    return Val2Sexp(V);
  }

  std::string SExpr(Value &V) { return SExpr(&V); }

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

  std::string visitStoreInst(StoreInst &I) {
    auto *GEP = dyn_cast<GetElementPtrInst>(I.getPointerOperand());
    assert(GEP->getNumIndices() == 1);
    std::string Ptr = visit(GEP);
    std::string Idx = SExpr(GEP->getOperand(1));
    std::string Val = SExpr(I.getValueOperand());
    auto StoreType = Type2String(I.getValueOperand()->getType());
    return "(update " + StoreType + " " + Ptr + " " + Idx + " " + Val + ")";
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

  std::string instToOp(Instruction &Op) {
    switch(Op.getOpcode()) {
    default:
      llvm_unreachable("unknown opcode.");
    case Instruction::Add:
    case Instruction::FAdd:
      return "+";
    case Instruction::Mul:
    case Instruction::FMul:
      return "*";
    case Instruction::FNeg:
      return "-";
    case Instruction::ICmp:
      auto Pred = dyn_cast<ICmpInst>(&Op)->getSignedPredicate();
      if (Pred == CmpInst::Predicate::ICMP_SGT)
        return ">";
      llvm_unreachable("unsupported ICmp predicate.");
    }
  }

  std::string visitBinaryOperator(BinaryOperator &I) {
    auto Left = SExpr(I.getOperand(0));
    auto Right = SExpr(I.getOperand(1));
    auto Op = instToOp(I);
    return "(" + Op + " " + Left + " " + Right + ")";
  }

  std::string visitUnaryOperator(UnaryOperator &I) {
    auto Input = SExpr(I.getOperand(0));
    auto Op = instToOp(I);
    return "(" + Op + " " + Input + ")";
  }

  std::string visitIntrinsicInst(IntrinsicInst &I) {
    switch (I.getIntrinsicID()) {
    default:
    llvm_unreachable("unsupported intrinsic.");
    case Intrinsic::fmuladd:
      auto A = SExpr(I.getOperand(0));
      auto B = SExpr(I.getOperand(1));
      auto C = SExpr(I.getOperand(2));
      return "(+ (* " + A + " " + B + ") " + C + ")";

    }
  }

  std::string visitICmpInst(ICmpInst &I) {
    auto Left = SExpr(I.getOperand(0));
    auto Right = SExpr(I.getOperand(1));
    auto Cmp = instToOp(I);
    return "(" + Cmp + " " + Left + " " + Right + ")";
  }

  std::string visitInstruction(Instruction &I) { return visit(I); }
};

class ExecutorDense : public Executor {
public:
  DenseMap<Value *, Tensor *> &TensorMap;
  ExecutorDense(DenseMap<Value *, Tensor *> &TensorMap) : TensorMap(TensorMap) {}

  std::string visitLoadInst(LoadInst &I) {
    Tensor *T = TensorMap[&I];
    assert(T != nullptr && "all loads must be covered.");
    return T->toString();
//    // try to construct tensors optimistically
//    auto *GEP = dyn_cast<GetElementPtrInst>(I.getPointerOperand());
//    assert(GEP->getNumIndices() == 1);
//    std::string Ptr = visit(GEP);
//    std::string Idx;
//    if (auto *Index = dyn_cast<Instruction>(GEP->getOperand(1)))
//      Idx = visit(Index);
//    else
//      Idx = getNameOrAsOperand(GEP->getOperand(1));
//    auto LoadType = Type2String(I.getType());
//    return "(tensor dense " + LoadType + " " + Ptr + " " + Idx + ")";
  }
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

raw_ostream &operator<<(raw_ostream &os, Tensor const &t) {
  std::string output = Format2String(t.Kind) + "(<";
  for (size_t i = 0; i < t.Shape.size(); ++i) {
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
  CSR(std::vector<Value *> Shape, Type *T, Value *Root, Value *Row, Value *Col)
      : Tensor(Shape, Root, T, StorageKind::CSR), Row(Row), Col(Col) {}
  Value *Row = nullptr;
  Value *Col = nullptr;
  static bool classof(const Tensor *T) {
    return T->getKind() == StorageKind::CSR;
  }
};

enum LevelTypeEnum { COMPRESSED, DENSE, UNKNOWN };

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
  std::vector<Value*> CoordArrays;
};

bool findCrd(Value *Inst, Value **Crd) {
  std::function<bool(Value *, Value *, int, SmallPtrSet<Value *, 4>)> DFS;
  DFS = [&Crd, &DFS](Value *V, Value *PrevLoad, int Loads,
                     SmallPtrSet<Value *, 4> Visited) {
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

// bool findCrd(Value *Inst, Value **Crd) {
//   std::vector<Value*> Stack;
//   SmallPtrSet<Value*, 4> Visited;
//   Stack.push_back(Inst);
//   int LoadCount = 0;
//   Value *PrevLoad = nullptr;
//   while (!Stack.empty()) {
//     auto *ToVisit = Stack.back();
//     Stack.pop_back();
//     if (!Visited.contains(ToVisit)) {
//       Visited.insert(ToVisit);
//       if (auto *Load = dyn_cast<LoadInst>(ToVisit)) {
//         if (LoadCount++ == 1) {
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

void makeLevelBounds(LoopNest *LN, ScalarEvolution *SE,
                     std::vector<LevelBounds> &Levels) {
  DataLayout DL = SE->getDataLayout();
  //  PHINode *PrevLevel = nullptr;
  for (auto *Loop : LN->getLoops()) {
    auto Bounds = Loop->getBounds(*SE);
    if (!Bounds.has_value())
      continue;
    auto *IndVar = Loop->getInductionVariable(*SE);
    LLVM_DEBUG(dbgs() << getNameOrAsOperand(IndVar) << " = ["
                      << Bounds->getInitialIVValue() << ", "
                      << Bounds->getFinalIVValue() << ") -> \n");

    //    std::vector<Value*> Uses;
    //    followUses(IndVar, Uses);
    //    for (auto *V : Uses) {
    //      LLVM_DEBUG(dbgs() << *V << "\n");
    //    }

    Value *LowerBound = &Bounds->getInitialIVValue();
    Value *UpperBound = &Bounds->getFinalIVValue();

    bool IsZero = match(LowerBound, m_ZeroInt());
    //    bool IsInt = isa<ConstantInt>(UpperBound) ||
    //    isa<Argument>(UpperBound);
    // TODO handle loads better (make sure that bounds are invariant)
    bool IsInt = UpperBound->getType()->getTypeID() == IntegerType::IntegerTyID;
    if (IsZero && IsInt) {
      LLVM_DEBUG(dbgs() << "dense\n");
      Levels.push_back({DENSE, IndVar, LowerBound, UpperBound});
      //      PrevLevel = IndVar;
      continue;
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
          Levels.push_back({COMPRESSED, IndVar, LowerBound, UpperBound,
                            IndexExpr, LowPtrBase});
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
      std::string Pred = CmpInst::getPredicateName(ICmp->getPredicate()).str();
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

template <> struct MappingTraits<Instruction *> {
  static void mapping(IO &io, Instruction *&I) {
    EmptyContext Ctx;
    yamlize(io, I, false, Ctx);
    //    io.mapRequired("op", I->getOpcodeName());
  }
};

template <> struct SequenceTraits<std::vector<Atom>> {
  static size_t size(IO &io, std::vector<Atom> &list) { return list.size(); }
  static Atom &element(IO &io, std::vector<Atom> &list, size_t index) {
    return list[index];
  }
};

template <> struct SequenceTraits<std::vector<::Node>> {
  static size_t size(IO &io, std::vector<::Node> &list) { return list.size(); }
  static ::Node &element(IO &io, std::vector<::Node> &list, size_t index) {
    return list[index];
  }
};

template <> struct SequenceTraits<std::vector<BBNode>> {
  static size_t size(IO &io, std::vector<BBNode> &list) { return list.size(); }
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

template <> struct MappingTraits<Tensor *> {
  static void mapping(IO &io, Tensor *&T) {
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
template <> struct SequenceTraits<std::vector<Tensor *>> {
  static size_t size(IO &io, std::vector<Tensor *> &list) {
    return list.size();
  }
  static Tensor *&element(IO &io, std::vector<Tensor *> &list, size_t index) {
    return list[index];
  }
};

// template <> struct MappingTraits<LevelBounds> {
//   static void mapping(IO &io, LevelBounds &LB) {
//     std::string IndVar = getNameOrAsOperand(LB.Iterator);
//     std::string LevelType = printLevelType(LB.LevelType);
//     io.mapRequired("indvar", LB.);
//     io.mapRequired("nodes", BN.Nodes);
//   }
// };
} // namespace llvm::yaml

void allLoadsInCurrentScope(Loop *L, SmallPtrSet<LoadInst *, 4> &Loads) {
  for (auto *BB : L->blocks()) {
    for (auto &I : *BB) {
      if (auto *Load = dyn_cast<LoadInst>(&I)) {
        Loads.insert(Load);
      }
    }
  }
}

std::string buildExpression(Value *LiveOut, PHINode *Iterator,
                            RecurrenceDescriptor &RD,
                            DenseMap<Value *, LevelBounds> &LevelMap,
                            DenseMap<Value *, Tensor *> &TensorMap) {
  if (RD.getRecurrenceKind() == RecurKind::None) {
    Executor E;
    return E.SExpr(LiveOut);
  } else if (RD.getRecurrenceKind() == RecurKind::FMulAdd) {
    auto *I = dyn_cast<Instruction>(LiveOut);
    Executor E;
    std::string Astr = E.visit(cast<Instruction>(I->getOperand(0)));
    std::string Bstr = E.visit(cast<Instruction>(I->getOperand(1)));
    return "(+ (* " + Astr + " " + Bstr + "))";
  } else {
    llvm_unreachable("unknown recurrence kind.");
  }
}

std::string buildDenseExpression(Value *LiveOut, PHINode *Iterator,
                                 RecurrenceDescriptor &RD,
                                 DenseMap<Value *, LevelBounds> &LevelMap,
                                 DenseMap<Value *, Tensor *> &TensorMap,
                                 std::string &Inputs) {
  if (RD.getRecurrenceKind() == RecurKind::None) {
    ExecutorDense E(TensorMap);
    return E.SExpr(LiveOut);
  } else if (RD.getRecurrenceKind() == RecurKind::FMulAdd) {
    auto *I = dyn_cast<Instruction>(LiveOut);
    Tensor *A = TensorMap[I->getOperand(0)];
    Tensor *B = TensorMap[I->getOperand(1)];
    SmallPtrSet<Value *, 4> Ins;
    for (auto *S : A->Shape)
      if (LevelMap[S].Iterator != Iterator)
        Ins.insert(S);
    for (auto *S : B->Shape)
      if (LevelMap[S].Iterator != Iterator)
        Ins.insert(S);
    Inputs = "(";
    auto It = Ins.begin();
    while (It != Ins.end()) {
      Inputs += Val2Sexp(*It);
      if (++It != Ins.end())
        Inputs += " ";
    }
    Inputs += ")";
    std::string Astr = A->toString();
    std::string Bstr = B->toString();
    return "(+ (* " + Astr + " " + Bstr + "))";
  } else {
    llvm_unreachable("unknown recurrence kind.");
  }
}

std::string makeDense(LevelBounds &LB) {
  std::string Map = "(table ";
  Executor E;
  for (auto *Crd : LB.CoordArrays) {
    std::string Left = E.SExpr(Crd);
    std::string Right = E.SExpr(LB.Iterator);
    Map += "(" + Left + " " + Right + ")";
  }
  return Map + ")";
}

void emitFold(raw_fd_ostream &FS, Loop *L, Value *LiveOut, PHINode *Iterator, RecurrenceDescriptor &RD,
              DenseMap<Value *, LevelBounds> &LevelMap,
              DenseMap<Value *, Tensor *> &TensorMap) {
  std::string Total;
  Total += "(loop \"" + L->getHeader()->getName().str() + "\"\n\t";
  // Name map
  std::string Names = "(table (" + Val2Sexp(Iterator) + " " + Val2Sexp(Iterator, ".d") + "))";
//  LLVM_DEBUG(dbgs() << Names << "\n");
  Total += "(namemap \n\t\t" + Names + ")\n\t";
  // Coordinate map
  std::string CrdMap = makeDense(LevelMap[Iterator]);
//  LLVM_DEBUG(dbgs() << CrdMap << "\n");
  Total += "(crdmap \n\t\t" + CrdMap + ")\n\t";
  // Val map
  // 1. find all the sparse inputs
  // 2. map to a dense version
  std::string ValMap = "(table ";
  Executor E;
  SmallPtrSet<Value*, 4> Loads;
  makeTopLevelInputs(LiveOut, Loads);
  for (auto *V : Loads) {
    auto *T = TensorMap[V];
    if (T != nullptr && isa<CSR>(T)) {
      std::string Left = E.SExpr(V);
      std::string Right = T->toString();
      ValMap += "(" + Left + " " + Right + ")";
    }
  }
  ValMap += ")";
//  LLVM_DEBUG(dbgs() << ValMap << "\n");
  Total += "(valmap \n\t\t" + ValMap + ")\n\t";
  std::string End;
  auto *StartVal = RD.getRecurrenceStartValue().getValPtr();
  LevelBounds &Bounds = LevelMap[Iterator];
  // emit sync
//  std::string Sync = "(and ";
//  for (auto *Crd : Bounds.CoordArrays) {
//    std::string Left = E.SExpr(Crd);
//    std::string Right = E.SExpr(Bounds.Iterator);
//    Sync += "(= " + Left + " " + Right + ")";
//  }
//  Sync += " ";
//  SmallPtrSet<Value*, 4> Loads;
//  makeTopLevelInputs(LiveOut, Loads);
//  for (auto *V : Loads) {
//    auto *T = TensorMap[V];
//    if (T != nullptr && isa<CSR>(T)) {
//      std::string Left = E.SExpr(V);
//      std::string Right = T->toString();
//      Sync += "(= " + Left + " " + Right + ")";
//    }
//  }
//  Sync += ")";
//  LLVM_DEBUG(dbgs() << Sync << "\n");
  auto *LowerBound = Bounds.LowerBound;
  auto *IndVar = Iterator;
  auto *UpperBound = Bounds.UpperBound;
  std::string Expr = "(fold ";
  Expr += Val2Sexp(StartVal) + " ";
  Expr += Val2Sexp(LowerBound) + " ";
  Expr += Val2Sexp(IndVar) + " ";
  Expr += Val2Sexp(UpperBound) + " ";
  Expr += buildExpression(LiveOut, Iterator, RD, LevelMap, TensorMap);
  Expr += ")";
//  LLVM_DEBUG({ dbgs() << Expr << "\n"; });
  Total += "(src \n\t\t" + Expr + ")\n\t";
  // now the dense version
  std::string DenseExpr = "(fold ";
  std::string DenseLowerBound, DenseUpperBound;
  if (LevelMap[Iterator].LevelType == COMPRESSED) {
    DenseLowerBound = "(int 0)";
    DenseUpperBound = "(int " + getNameOrAsOperand(Iterator) + ".end)";
  } else {
    DenseLowerBound =
        "(int " + getNameOrAsOperand(LevelMap[Iterator].LowerBound) + ")";
    DenseUpperBound =
        "(int " + getNameOrAsOperand(LevelMap[Iterator].UpperBound) + ")";
  }
  DenseExpr += Val2Sexp(StartVal) + " ";
  DenseExpr += DenseLowerBound + " ";
  DenseExpr += Val2Sexp(IndVar) + " ";
  DenseExpr += DenseUpperBound + " ";
  std::string Inputs;
  DenseExpr += buildDenseExpression(LiveOut, Iterator, RD, LevelMap, TensorMap, Inputs);
  DenseExpr += ")";
//  LLVM_DEBUG({ dbgs() << DenseExpr << "\n"; });
  Total += "(target \n\t\t" + DenseExpr + "))\n";
  LLVM_DEBUG({
      dbgs() << Total << "\n";
  });
  FS << Total;
}

std::string nameMap(PHINode *Iterator, DenseMap<Value *, LevelBounds> &LevelMap) {
  if (LevelMap[Iterator].LevelType == COMPRESSED)
    return "(table (" + Val2Sexp(Iterator) + " " + Val2Sexp(Iterator, ".d") + "))";
  return "(table )";
}

std::string valMap(Value *LiveOut, LoopInfo *LI, Loop *L, DenseMap<Value *, Tensor *> &TensorMap) {
  std::string ValMap = "(table ";
  Executor E;
  SmallPtrSet<Value*, 4> Loads;
  makeTopLevelInputs(LiveOut, Loads);
  for (auto *V : Loads) {
    if (LI->getLoopFor(cast<LoadInst>(V)->getParent()) != L)
      continue;
    auto *T = TensorMap[V];
    if (T != nullptr && isa<CSR>(T)) {
      std::string Left = E.SExpr(V);
      std::string Right = T->toString();
      ValMap += "(" + Left + " " + Right + ")";
    }
  }
  ValMap += ")";
  return ValMap;
}

void emitMap(raw_fd_ostream &FS, Loop *L, LoopInfo *LI, Value *LiveOut, PHINode *Iterator, RecurrenceDescriptor &RD,
             DenseMap<Value *, LevelBounds> &LevelMap,
             DenseMap<Value *, Tensor *> &TensorMap) {
  // TODO merge with emitFold
  std::string Total;
  Total += "(loop \"" + L->getHeader()->getName().str() + "\"\n\t";
  // Name Map
  std::string Names = nameMap(Iterator, LevelMap);
  Total += "(namemap \n\t\t" + Names + ")\n\t";
  // Coord map
  std::string CrdMap = makeDense(LevelMap[Iterator]);
  Total += "(crdmap \n\t\t" + CrdMap + ")\n\t";
  Total += "(valmap \n\t\t" + valMap(LiveOut, LI, L, TensorMap) + ")\n\t";

  // first original
  std::string InputCode;
  std::string Idx = Val2Sexp(Iterator);
  {
    std::string Start = Val2Sexp(LevelMap[Iterator].LowerBound);
    std::string End = Val2Sexp(LevelMap[Iterator].UpperBound);
    std::string Func = buildExpression(LiveOut, Iterator, RD, LevelMap, TensorMap);
    InputCode = "(map " + Start + " " + Idx + " " + End + " " + Func + ")";
  }
  Total += "(src \n\t\t" + InputCode + ")\n\t";
  // Then dense
  std::string DenseCode;
  {
    std::string Start = "(int 0)";
    std::string End;
    if (LevelMap[Iterator].LevelType == COMPRESSED)
      End = getNameOrAsOperand(Iterator) + ".end";
    else
      End = getNameOrAsOperand(LevelMap[Iterator].UpperBound);
    End = "(int " + End + ")"; // TODO check this is true
    std::string Inputs;
    std::string Func = buildDenseExpression(LiveOut, Iterator, RD, LevelMap, TensorMap, Inputs);
    DenseCode = "(map " + Start + " " + Idx + " " + End + " " + Func + ")";
  }
  Total += "(target \n\t\t" + DenseCode + "))\n";
  LLVM_DEBUG({
      dbgs() << Total << "\n";
  });
  FS << Total;
}

enum Property { FULL, ORDERED, UNIQUE, BRANCHLESS, COMPACT };

void findFirstDep(Value *Operand, SmallPtrSetImpl<Value *> &Inputs) {
  std::queue<Value *> Queue;
  SmallPtrSet<Value *, 5> Visited;
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

bool detectCSC(LoopInfo *LI, Value *Root, Value **Row, Value **Col, Value **Val,
               DenseMap<Value *, LevelBounds> &LevelMap) {
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

bool detectCSR(LoopInfo *LI, Value *Root, Value **Row, Value **Col, Value **Val,
               Value **I, Value **J, DenseMap<Value *, LevelBounds> &LevelMap) {
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
    LevelMap[*J].CoordArrays.push_back(*Col); // TODO dangerous! fix
    auto JBounds = LevelMap[*J];
    JBounds.LevelType = DENSE;
    LevelMap[*Col] = JBounds;
  }
  return true;
}

bool detectDense2D(LoopInfo *LI, ScalarEvolution *SE, LoadInst *Root, Value **A,
                   Value **Pk_1, Value **Nk, Value **Ik,
                   DenseMap<Value *, LevelBounds> &LevelMap) {
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
    if (!LI->getLoopFor(LevelMap[J].Iterator->getParent())
             ->isLoopInvariant(*Nk))
      return false;
    Next = skipCasts(Mul->getOperand(0));
  }

  if (LevelMap.contains(Next) && LevelMap[Next].LevelType == DENSE) {
    *Pk_1 = LevelMap[Next].Iterator;
  } else {
    return false;
  }

  return true;

  //  const SCEV *AccessFn = SE->getSCEVAtScope(getPointerOperand(Root),
  //  LI->getLoopFor(Root->getParent())); const SCEV *BasePointer =
  //  dyn_cast<SCEVUnknown>(SE->getPointerBase(AccessFn)); AccessFn =
  //  SE->getMinusSCEV(AccessFn, BasePointer); auto *TryCast =
  //  dyn_cast<SCEVAddRecExpr>(AccessFn); LLVM_DEBUG(dbgs() << *Root << " ==> "
  //  << *TryCast << "\n"); SmallVector<const SCEV*> Subscripts, Sizes;
  //  delinearize(*SE, TryCast, Subscripts, Sizes, SE->getElementSize(Root));
  //  LLVM_DEBUG({
  //      for (auto *S : Subscripts)
  //        dbgs() << *S << "\n";
  //      for (auto *S : Sizes)
  //        dbgs() << *S << "\n";
  //  });

  return false;
}

bool detectDense1D(LoopInfo *LI, ScalarEvolution *SE, LoadInst *Root, Value **x,
                   Value **Ik, DenseMap<Value *, LevelBounds> &LevelMap) {
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
                   DenseMap<Value *, Tensor *> &TensorMap) {
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

void makeTopLevelInputs(Value *LiveOut, SmallPtrSetImpl<Value *> &Inputs) {
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
  SmallVector<Value *> StoreInsts;
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
    assert(ScalarLO->getNumIncomingValues() == 1 &&
           "only one incoming value allowed.");
    return ScalarLO->getOperand(0);
  }
  return StoreInsts[0];
}

//class Translate {
//public:
//
//  Translate(LoopInfo *LI, ScalarEvolution *SE, MemorySSA *MSSA)
//      : LI(LI), SE(SE), MSSA(MSSA) {
//    Out = new raw_string_ostream(StrOutput);
//  }
//
//  ~Translate() {
//    delete Out;
//  }
//
//  void visit(Function *F) {
//    analyzeMemory(F);
//    auto *Entry = &F->getEntryBlock();
//    visitBB(Entry, nullptr);
//  }
//
//private:
//  LoopInfo *LI = nullptr;
//  ScalarEvolution *SE = nullptr;
//  MemorySSA *MSSA = nullptr;
//  SmallPtrSet<BasicBlock*, 10> Visited = {};
//  int Indent = 0;
//  std::string StrOutput = "";
//  raw_ostream *Out;
//  const MemoryDef *MemInst = nullptr;
//  Value *MemPtr = nullptr;
//
//  raw_ostream &out() {
//    return *Out;
//  }
//
//  void indent() {
//    Indent++;
//  }
//
//  void deindent() {
//    Indent--;
//  }
//
//  std::string prefix() {
//    std::string Prefix = "";
//    for (int i=0; i < Indent; ++i) Prefix += "\t";
//    return Prefix;
//  }
//
//  void analyzeMemory(Function *F) {
//    for (auto &BB : *F) {
//      const auto *Defs = MSSA->getBlockDefs(&BB);
//      if (Defs) {
//        for (const auto &MA : *Defs) {
//          if (auto *D = dyn_cast<MemoryDef>(&MA)) {
//            assert(!MemPtr && "only 1 stored ptr supported right now");
//            MemInst = D;
//          }
//        }
//      }
//    }
//    if (MemInst) {
//      auto *Ptr = SE->getSCEV(MemInst->getMemoryInst()->getOperand(1));
//      auto *Base = dyn_cast<SCEVUnknown>(SE->getPointerBase(Ptr));
//      MemPtr = Base->getValue();
//      dbgs() << getNameOrAsOperand(MemPtr) << " is modified\n";
//    }
//  }
//
//  void visitBB(BasicBlock *From, BasicBlock *To) {
//    Visited.insert(From);
//    if (LI->isLoopHeader(From)) {
//      visitLoop(LI->getLoopFor(From), To);
//    } else {
//      //    out() << Prefix << From->getName() << ":\n";
//      for (auto &I : *From) {
//        if (&I == From->getTerminator()) break;
//        visitInstruction(&I);
//      }
//      auto *T = From->getTerminator();
////      if (auto *Ret = dyn_cast<ReturnInst>(T)) {
////        visitRet(Ret);
////      }
//      if (From == To)
//        return;
//      wave(T, To);
//    }
//  }
//
//  void visitRet(ReturnInst *Ret) {
//    if (Ret->getType()->isVoidTy())
//      out() << prefix() << getNameOrAsOperand(MemPtr) << "\n";
//    else
//      out() << prefix() << getNameOrAsOperand(Ret->getReturnValue()) << "\n";
//  }
//
//  void wave(Instruction *Terminator, BasicBlock *To) {
//    if (auto *Br = dyn_cast<BranchInst>(Terminator)) {
//      for (auto *O : Br->successors()) {
//        if (all_of(predecessors(O), [&](BasicBlock *P) {
//              if (!Visited.contains(P)) {
//                auto *L = LI->getLoopFor(O);
//                return L && L->getLoopLatch() == P;
//              }
//              return true;
//            }))
//          visitBB(O, To);
//      }
//    }
//  }
//
//  void visitInstruction(Instruction *I) {
//    if (auto *Phi = dyn_cast<PHINode>(I)) {
//      // collect pred. branches
//      out() << prefix() << "let " << getNameOrAsOperand(I) << " = ";
//      if (Phi->getNumIncomingValues() == 1) {
//        out() << getNameOrAsOperand(Phi->getIncomingValue(0)) << " ";
//      } else {
//        for (int V = 0; V < Phi->getNumIncomingValues(); ++V) {
//          auto *Val = Phi->getIncomingValue(V);
//          auto *BB = Phi->getIncomingBlock(V);
//          out() << "if (";
//          auto *T = BB->getTerminator();
//          if (auto *Br = dyn_cast_or_null<BranchInst>(T)) {
//            if (Br->isUnconditional())
//              out() << "true";
//            else {
//              if (Br->getSuccessor(1) == BB) // true
//                out() << getNameOrAsOperand(Br->getCondition());
//              else
//                out() << "!" << getNameOrAsOperand(Br->getCondition());
//            }
//          }
//          out() << ") then " << getNameOrAsOperand(Val) << " ";
//          if (V + 1 < Phi->getNumIncomingValues())
//            out() << "else ";
//        }
//      }
//      out() << "in\n";
//    } else {
//      out() << prefix() << "let " << *I << " in\n";
//    }
//  }
//
//  void visitLoop(Loop *L, BasicBlock *To) {
//    auto *IV = L->getInductionVariable(*SE);
//    auto B = L->getBounds(*SE);
//    auto *Header = L->getHeader();
//    auto *T = Header->getTerminator();
//    auto *Latch = L->getLoopLatch();
//    auto FoldName = Header->getName().str();
//
//    out() << prefix() << "let " << FoldName << " = λ";
//    std::string ArgNames;
//    auto *MPhi = MSSA->getMemoryAccess(Header);
//    if (MPhi) {
//      ArgNames += getNameOrAsOperand(MemPtr) + ".old ";
//    }
//    for (auto &P : Header->phis()) {
//      if (&P == IV) continue;
//      ArgNames += getNameOrAsOperand(&P) + " ";
//    }
//    out() << ArgNames << getNameOrAsOperand(IV) << ".\n";
//
//    indent();
//
//    if (Header == Latch) {
//      Executor E;
//      // outputs
//      auto *LiveOut = &*L->getExitBlock()->phis().begin();
//      assert(!(LiveOut && MPhi) && "simultaneous memory and scalar output not supported right now");
//      if (LiveOut) {
//        out() << prefix() << E.SExpr(LiveOut->getIncomingValue(0));
//        //      out() << prefix() << getNameOrAsOperand(LiveOut->getIncomingValue(0));
//      } else {
//        out() << prefix() << E.SExpr(MemInst->getMemoryInst());
//        //      out() << prefix() << getNameOrAsOperand(MemPtr) + ".new";
//      }
//      out() << "\n";
//    } else {
//      // other code in loop body ending at latch
//      wave(T, Latch);
//    }
//
//    indent();
//
//    out() << prefix() << "let r = fold (";
//    // grab phis
//    ListSeparator LS(", ");
//    std::string OutNames;
//    if (MPhi) {
//      // initial val
//      auto *Incoming = MPhi->getIncomingValueForBlock(L->getLoopPreheader());
//      auto FreshMem = getNameOrAsOperand(MemPtr) + "." + Incoming->getBlock()->getName().str();
//      out() << LS << FreshMem;
//      // ongoing val
//      OutNames += getNameOrAsOperand(MemPtr) + "." + L->getLoopLatch()->getName().str();
//    }
//
//    for (auto &P : Header->phis()) {
//      if (&P == IV)
//        continue;
//      if (&P != &*Header->phis().begin() || MPhi)
//        OutNames += ", ";
//      out() << LS << getNameOrAsOperand(P.getIncomingValueForBlock(L->getLoopPreheader()));
//      OutNames += getNameOrAsOperand(P.getIncomingValueForBlock(L->getLoopLatch()));
//    }
//
//    out() << ") " << FoldName << " Range(" << getNameOrAsOperand(&B->getInitialIVValue())
//           << ", " << getNameOrAsOperand(&B->getFinalIVValue()) << ") in\n";
//
//    indent();
//    out() << prefix() << "let " << OutNames << " = r in\n";
//    indent();
//    if (MPhi)
//      out() << prefix() << OutNames;
//    else {
//      auto *LiveOut = &*L->getExitBlock()->phis().begin();
//      out() << prefix() << getNameOrAsOperand(LiveOut->getIncomingValue(0));
//    }
//    out() << "\n";
//
//    auto *Exit = L->getExitBlock();
//    visitBB(Exit, To);
//
//    deindent();
//    deindent();
//    deindent();
//    deindent();
//  }
//
//  friend raw_ostream &operator<<(raw_ostream &OS, const Translate &T);
//};
//
//raw_ostream &operator<<(raw_ostream &OS, const Translate &T) {
//  return OS << T.StrOutput;
//}

//void TranslateBB(std::string Prefix, BasicBlock *From, BasicBlock *To, SmallPtrSetImpl<BasicBlock*> &Visited, LoopInfo *LI, ScalarEvolution *SE);
//
//void TranslateWave(std::string Prefix, Instruction *Terminator, SmallPtrSetImpl<BasicBlock*> &Visited, BasicBlock *To, LoopInfo *LI, ScalarEvolution *SE) {
//  if (auto *Br = dyn_cast<BranchInst>(Terminator)) {
//    for (auto *O : Br->successors()) {
//      if (all_of(predecessors(O), [&](BasicBlock *P) {
//            if (!Visited.contains(P)) {
//              auto *L = LI->getLoopFor(O);
//              return L && L->getLoopLatch() == P;
//            }
//            return true;
//          }))
//        TranslateBB(Prefix, O, To, Visited, LI, SE);
//    }
//  }
//}
//
//void TranslateInstruction(std::string Prefix, Instruction *I) {
//  if (auto *Phi = dyn_cast<PHINode>(I)) {
//    // collect pred. branches
//    dbgs() << Prefix << "let " << getNameOrAsOperand(I) << " = ";
//    for (int V = 0;  V < Phi->getNumIncomingValues(); ++V) {
//      auto *Val = Phi->getIncomingValue(V);
//      auto *BB = Phi->getIncomingBlock(V);
//      dbgs() << "if (";
//      auto *T = BB->getTerminator();
//      if (auto *Br = dyn_cast_or_null<BranchInst>(T)) {
//        if (Br->isUnconditional())
//          dbgs() << "true";
//        else {
//          if (Br->getSuccessor(1) == BB) // true
//            dbgs() << getNameOrAsOperand(Br->getCondition());
//          else
//            dbgs() << "!" << getNameOrAsOperand(Br->getCondition());
//        }
//      }
//      dbgs() << ") then " << getNameOrAsOperand(Val) << " ";
//      if (V + 1 < Phi->getNumIncomingValues())
//        dbgs() << "else ";
//    }
//    dbgs() << "\n";
//  } else {
//    dbgs() << Prefix << "let " << *I << " in\n";
//  }
//}
//
//void TranslateLoop(std::string Prefix, Loop *L, LoopInfo *LI, ScalarEvolution *SE, SmallPtrSetImpl<BasicBlock*> &Visited) {
//  auto *IV = L->getInductionVariable(*SE);
//  auto B = L->getBounds(*SE);
//  auto *Header = L->getHeader();
//  auto *T = Header->getTerminator();
//  auto *Latch = L->getLoopLatch();
//
//  dbgs() << Prefix << "let f = λ";
//  std::string ArgNames;
//  for (auto &P : Header->phis()) {
//    if (&P == IV) continue;
//    ArgNames += getNameOrAsOperand(&P) + " ";
//  }
//  dbgs() << ArgNames << getNameOrAsOperand(IV) << ".\n";
//
//  auto NewPrefix = Prefix + "\t";
//
//  if (Header == Latch) {
//    auto *I = Header->getFirstNonPHI();
//    while (I != Header->getTerminator()) {
//      TranslateInstruction(NewPrefix, I);
//      I = I->getNextNode();
//    }
//  } else {
//    // other code in loop body ending at latch
//    TranslateWave(NewPrefix, T, Visited, Latch, LI, SE);
//  }
//
//  NewPrefix += "\t";
//
//  dbgs() << NewPrefix << "let r = fold (";
//  // grab phis
//  ListSeparator LS(", ");
//  std::string OutNames;
//  for (auto &P : Header->phis()) {
//    if (&P == IV)
//      continue;
//    dbgs() << LS << getNameOrAsOperand(P.getIncomingValueForBlock(L->getLoopPreheader()));
//    OutNames += getNameOrAsOperand(P.getIncomingValueForBlock(L->getLoopLatch())) + ", ";
//  }
//  dbgs() << ") f Range(" << getNameOrAsOperand(&B->getInitialIVValue())
//         << ", " << getNameOrAsOperand(&B->getFinalIVValue()) << ") in\n";
//  dbgs() << NewPrefix << "\t" << "let " << OutNames << "= r in\n";
//
//}
//
//void TranslateBB(std::string Prefix, BasicBlock *From, BasicBlock *To, SmallPtrSetImpl<BasicBlock*> &Visited, LoopInfo *LI, ScalarEvolution *SE) {
//  Visited.insert(From);
//  if (LI->isLoopHeader(From)) {
//    TranslateLoop(Prefix, LI->getLoopFor(From), LI, SE, Visited);
//    auto *Exit = LI->getLoopFor(From)->getExitBlock();
//    TranslateBB(Prefix + "\t", Exit, To, Visited, LI, SE);
//  } else {
////    dbgs() << Prefix << From->getName() << ":\n";
//    for (auto &I : *From) {
//      if (&I == From->getTerminator()) break;
//      TranslateInstruction(Prefix, &I);
//    }
//    if (From == To)
//      return;
//    auto *T = From->getTerminator();
//    TranslateWave(Prefix, T, Visited, To, LI, SE);
//  }
//}
//void Translate(Function *F, LoopInfo *LI, ScalarEvolution *SE) {
//  auto *Entry = &F->getEntryBlock();
//  SmallPtrSet<BasicBlock*, 10> Visited;
//  TranslateBB("", Entry, nullptr, Visited, LI, SE);
//
//}

//std::string PhisAsParams(iterator_range<filter_iterator<BasicBlock>> Phis, PHINode *IV) {
//  std::string StrParam = "";
//  raw_string_ostream Params(StrParam);
//  ListSeparator LS(", ");
//  for (auto &Phi : Phis) {
//    Params << LS << getNameOrAsOperand(&Phi);
//  }
//  if (!Phis.empty())
//    Params << ", ";
//  Params << getNameOrAsOperand(IV);
//  return StrParam;
//}

//std::string PhisAsArgs(BasicBlock *Header, PHINode *IV) {
//  std::string Args = "";
//  for (auto &Phi : Header->phis()) {
//    if (IV == &Phi) continue;
//    if (&Phi != &*Header->phis().begin())
//      Args += ", ";
//    Args += getNameOrAsOperand(Phi.getIncomingValueForBlock());
//  }
//  if (!Header->phis().empty())
//    Params += ", ";
//  Params += getNameOrAsOperand(IV);
//}


class LambdaV2 {
public:
  LambdaV2(LoopInfo &LI, ScalarEvolution &SE, MemorySSA &MSSA)
      : LI(LI), SE(SE), MSSA(MSSA), ToLam(Inline()) {}


  void translate(Function &F) {
    analyzeMemory(&F);
    Exit2Loop.clear();
    Latch2Loop.clear();
    ReversePostOrderTraversal<Function*> RPOT(&F);
    SmallPtrSet<BasicBlock*, 5> Visited;

    // make first Abs
    Var Params(F.args());

    Params.dump();

    return;

    for (auto *BB : RPOT) {
      if (Visited.contains(BB))
        continue;
      Visited.insert(BB);
      if (Latch2Loop[BB]) {
        latch(BB);
      }
      else if (Exit2Loop[BB]) {
        exit(BB);
      }
      else if (LI.isLoopHeader(BB)) {
        auto *Header = BB;
        auto *L = LI.getLoopFor(Header);
        auto *Latch = L->getLoopLatch();
        auto *ExitBlock = L->getExitBlock();
        auto *IV = L->getInductionVariable(SE);
        auto Params = make_filter_range(Header->phis(),
                                        [IV](PHINode &P) { return &P != IV; });
        Exit2Loop[ExitBlock] = L;
        Latch2Loop[Latch] = L;
        auto *MemPhi = MSSA.getMemoryAccess(Header);
        auto LiveOuts = ExitBlock->phis();
        assert((!MemPhi || LiveOuts.empty()) && "simultaneous memory and scalar output not supported right now.");
        std::string StrParam = "";
        if (MemPhi) {
          auto *Clob = MSSA.getWalker()->getClobberingMemoryAccess(MemPhi);
          StrParam += getNameOrAsOperand(MemPtr) + " ";
        }
        {
          raw_string_ostream Ps(StrParam);
          ListSeparator LS(" ");
          for (auto &Phi : Params) {
            Ps << LS << getNameOrAsOperand(&Phi);
          }
          if (!Params.empty())
            Ps << " ";
          Ps << getNameOrAsOperand(IV);
        }

        dbgs() << Tabs << "let " << BB->getName() << " = λ" <<  StrParam << ". \n";

        if (Header != Latch)
          Tabs += "\t";
        else
          latch(Latch);
        dbgs() << " in\n";
      } else {
        bb(BB);
      }
    }
  }

private:
  LoopInfo &LI;
  ScalarEvolution &SE;
  MemorySSA &MSSA;
  const MemoryDef *MemInst = nullptr;
  Value *MemPtr = nullptr;
  DenseMap<BasicBlock*, Loop*> Exit2Loop;
  DenseMap<BasicBlock*, Loop*> Latch2Loop;
  Inline ToLam;
  std::string Tabs = "";

  Exp *phi(PHINode *P) {
    assert(P->getNumIncomingValues() == 2 && "only 2 incoming vals supported right now");
    auto *B1 = P->getIncomingBlock(0);
    auto *B2 = P->getIncomingBlock(1);
    auto *Br1 = dyn_cast<BranchInst>(B1->getTerminator());
    auto *Br2 = dyn_cast<BranchInst>(B2->getTerminator());
    auto *Then = Br1->isConditional() ? Br1 : Br2;
    auto *Else = Br1->isConditional() ? Br2 : Br1;
    assert(Else->isUnconditional() && "unsupported control flow.");
    auto *Cond = ToLam.run(Then->getCondition());
    if (Then->getOperand(1) == P->getParent()) // False target
      Cond = Builtin::mkNot(Cond);
    auto *True = ToLam.run(P->getIncomingValueForBlock(Then->getParent()));
    auto *False = ToLam.run(P->getIncomingValueForBlock(Else->getParent()));
    return new IfThen(Cond, True, False);
  }

  void bb(BasicBlock *BB) {
    std::vector<Exp*> Es;
    for (auto &P : BB->phis()) {
      auto *Left = ToLam.run(&P);
      auto *Right = phi(&P);
      dbgs() << Tabs << "let " << getNameOrAsOperand(&P) << " = ";
      phi(&P);
      dbgs() << " in\n";
    }
//    auto *I = BB->getFirstNonPHI();
//    auto *T = BB->getTerminator();
//    while (I && I != T) {
//      dbgs() << Tabs << "let " << getNameOrAsOperand(I) << " = " << E.SExpr(I) << " in\n";
//      I = I->getNextNode();
//    }
//    if (auto *Ret = dyn_cast<ReturnInst>(T)) {
//      if (!Ret->getReturnValue())
//        dbgs() << Tabs << getNameOrAsOperand(MemPtr) << "\n";
//      else
//        dbgs() << Tabs << getNameOrAsOperand(Ret->getReturnValue()) << "\n";
//    }
  }

  void exit(BasicBlock *Exit) {
    Executor E;
    Loop *L = Exit2Loop[Exit];
    auto *Header = L->getHeader();
    auto *IV = L->getInductionVariable(SE);
    auto B = L->getBounds(SE);
    auto Start = E.SExpr(B->getInitialIVValue());
    auto End = E.SExpr(B->getFinalIVValue());
    std::string Base = "";
    auto Params = make_filter_range(Header->phis(),
                                    [IV](PHINode &P) { return &P != IV; });
    std::string Args = "";
    for (auto &P : Params) {
      if (&P != &*Params.begin()) Args += ", ";
      Args += E.SExpr(P.getIncomingValueForBlock(L->getLoopPreheader()));
    }

    dbgs() << Tabs << "let " << getNameOrAsOperand(&*Exit->phis().begin()) << " = fold"
           << " (" << Args << ") "
           << L->getHeader()->getName() << " "
           << "Range(" << Start << ", " << End << ")" << " in\n";
  }

  void latch(BasicBlock *Latch) {
    Loop *L = Latch2Loop[Latch];
    auto LiveOuts = L->getExitBlock()->phis();
    Executor E;
    if (!LiveOuts.empty()) {
      for (auto &LO : LiveOuts)
        dbgs() << Tabs << E.SExpr(LO.getIncomingValue(0)) << " ";
    } else {
      auto *Inst = MemInst->getMemoryInst();
      if (LI.getLoopFor(Inst->getParent()) == L)
        dbgs() << Tabs << E.SExpr(MemInst->getMemoryInst()) << " ";
      else {
        // nearest clobber
        auto *LatchPhi = MSSA.getMemoryAccess(Latch);

      }
    }
    //    dbgs() << "\n";
  }

  void analyzeMemory(Function *F) {
    for (auto &BB : *F) {
      const auto *Defs = MSSA.getBlockDefs(&BB);
      if (Defs) {
        for (const auto &MA : *Defs) {
          if (auto *D = dyn_cast<MemoryDef>(&MA)) {
            assert(!MemPtr && "only 1 stored ptr supported right now");
            MemInst = D;
          }
        }
      }
    }
    if (MemInst) {
      auto *Ptr = SE.getSCEV(MemInst->getMemoryInst()->getOperand(1));
      auto *Base = dyn_cast<SCEVUnknown>(SE.getPointerBase(Ptr));
      MemPtr = Base->getValue();
      dbgs() << getNameOrAsOperand(MemPtr) << " is modified\n";
    }
  }
};

class Lambda {
public:
  Lambda(LoopInfo &LI, ScalarEvolution &SE, MemorySSA &MSSA)
      : LI(LI), SE(SE), MSSA(MSSA), ToLam(Inline()) {}


  void translate(Function &F) {
    analyzeMemory(&F);
    Exit2Loop.clear();
    Latch2Loop.clear();
    ReversePostOrderTraversal<Function*> RPOT(&F);
    SmallPtrSet<BasicBlock*, 5> Visited;

    // make first Abs
    Var Params1(F.args());


    std::string Params = "";
    for (auto &Arg : F.args()) {
      if (&Arg != &*F.arg_begin()) Params += " ";
      Params += getNameOrAsOperand(&Arg);
    }
    dbgs() << "let " << F.getName() << " = λ" << Params << ".\n";
    Tabs += "\t";

    for (auto *BB : RPOT) {
      if (Visited.contains(BB))
        continue;
      Visited.insert(BB);
      if (Latch2Loop[BB]) {
        Tabs.pop_back();
        latch(BB);
        dbgs() << " in\n";
      }
      else if (Exit2Loop[BB]) {
        exit(BB);
      }
      else if (LI.isLoopHeader(BB)) {
        auto *Header = BB;
        auto *L = LI.getLoopFor(Header);
        auto *Latch = L->getLoopLatch();
        auto *ExitBlock = L->getExitBlock();
        auto *IV = L->getInductionVariable(SE);
        auto Params = make_filter_range(Header->phis(),
                                        [IV](PHINode &P) { return &P != IV; });
        Exit2Loop[ExitBlock] = L;
        Latch2Loop[Latch] = L;
        auto *MemPhi = MSSA.getMemoryAccess(Header);
        auto LiveOuts = ExitBlock->phis();
        assert((!MemPhi || LiveOuts.empty()) && "simultaneous memory and scalar output not supported right now.");
        std::string StrParam = "";
        if (MemPhi) {
          auto *Clob = MSSA.getWalker()->getClobberingMemoryAccess(MemPhi);
          StrParam += getNameOrAsOperand(MemPtr) + " ";
        }
        {
          raw_string_ostream Ps(StrParam);
          ListSeparator LS(" ");
          for (auto &Phi : Params) {
            Ps << LS << getNameOrAsOperand(&Phi);
          }
          if (!Params.empty())
            Ps << " ";
          Ps << getNameOrAsOperand(IV);
        }

        dbgs() << Tabs << "let " << BB->getName() << " = λ" <<  StrParam << ". \n";

        if (Header != Latch)
          Tabs += "\t";
        else
          latch(Latch);
        dbgs() << " in\n";
      } else {
        bb(BB);
//        dbgs() << Tabs << BB->getName();
//        if (Latch2Loop[BB])
//          dbgs() << " (end " << Latch2Loop[BB]->getHeader()->getName() << ")";
//        dbgs() << "\n";
      }
    }
  }

private:
  LoopInfo &LI;
  ScalarEvolution &SE;
  MemorySSA &MSSA;
  const MemoryDef *MemInst = nullptr;
  Value *MemPtr = nullptr;
  DenseMap<BasicBlock*, Loop*> Exit2Loop;
  DenseMap<BasicBlock*, Loop*> Latch2Loop;
  Inline ToLam;
  std::string Tabs = "";

  void phi(PHINode *P) {
    Executor E;
    assert(P->getNumIncomingValues() == 2 && "only 2 incoming vals supported right now");
    auto *B1 = P->getIncomingBlock(0);
    auto *B2 = P->getIncomingBlock(1);
    auto *Br1 = dyn_cast<BranchInst>(B1->getTerminator());
    auto *Br2 = dyn_cast<BranchInst>(B2->getTerminator());
    auto *Then = Br1->isConditional() ? Br1 : Br2;
    auto *Else = Br1->isConditional() ? Br2 : Br1;
    assert(Else->isUnconditional() && "unsupported control flow.");
    auto Cond = getNameOrAsOperand(Then->getCondition());
    if (Then->getOperand(1) == P->getParent()) // False target
      Cond = "(not " + Cond + ")";
    dbgs() << "if " << Cond;
    dbgs() << " then " << E.SExpr(P->getIncomingValueForBlock(Then->getParent()));
    dbgs() << " else " << E.SExpr(P->getIncomingValueForBlock(Else->getParent()));
  }

  void bb(BasicBlock *BB) {
    Executor E;
    for (auto &P : BB->phis()) {
      dbgs() << Tabs << "let " << getNameOrAsOperand(&P) << " = ";
      phi(&P);
      dbgs() << " in\n";
    }
    auto *I = BB->getFirstNonPHI();
    auto *T = BB->getTerminator();
    while (I && I != T) {
      dbgs() << Tabs << "let " << getNameOrAsOperand(I) << " = " << E.SExpr(I) << " in\n";
      I = I->getNextNode();
    }
    if (auto *Ret = dyn_cast<ReturnInst>(T)) {
      if (!Ret->getReturnValue())
        dbgs() << Tabs << getNameOrAsOperand(MemPtr) << "\n";
      else
        dbgs() << Tabs << getNameOrAsOperand(Ret->getReturnValue()) << "\n";
    }
  }

  void exit(BasicBlock *Exit) {
    Executor E;
    Loop *L = Exit2Loop[Exit];
    auto *Header = L->getHeader();
    auto *IV = L->getInductionVariable(SE);
    auto B = L->getBounds(SE);
    auto Start = E.SExpr(B->getInitialIVValue());
    auto End = E.SExpr(B->getFinalIVValue());
    std::string Base = "";
    auto Params = make_filter_range(Header->phis(),
                                    [IV](PHINode &P) { return &P != IV; });
    std::string Args = "";
    for (auto &P : Params) {
      if (&P != &*Params.begin()) Args += ", ";
      Args += E.SExpr(P.getIncomingValueForBlock(L->getLoopPreheader()));
    }

    dbgs() << Tabs << "let " << getNameOrAsOperand(&*Exit->phis().begin()) << " = fold"
           << " (" << Args << ") "
           << L->getHeader()->getName() << " "
           << "Range(" << Start << ", " << End << ")" << " in\n";
  }

  void latch(BasicBlock *Latch) {
    Loop *L = Latch2Loop[Latch];
    auto LiveOuts = L->getExitBlock()->phis();
    Executor E;
    if (!LiveOuts.empty()) {
      for (auto &LO : LiveOuts)
        dbgs() << Tabs << E.SExpr(LO.getIncomingValue(0)) << " ";
    } else {
      auto *Inst = MemInst->getMemoryInst();
      if (LI.getLoopFor(Inst->getParent()) == L)
        dbgs() << Tabs << E.SExpr(MemInst->getMemoryInst()) << " ";
      else {
        // nearest clobber
        auto *LatchPhi = MSSA.getMemoryAccess(Latch);

      }
    }
//    dbgs() << "\n";
  }

  void analyzeMemory(Function *F) {
    for (auto &BB : *F) {
      const auto *Defs = MSSA.getBlockDefs(&BB);
      if (Defs) {
        for (const auto &MA : *Defs) {
          if (auto *D = dyn_cast<MemoryDef>(&MA)) {
            assert(!MemPtr && "only 1 stored ptr supported right now");
            MemInst = D;
          }
        }
      }
    }
    if (MemInst) {
      auto *Ptr = SE.getSCEV(MemInst->getMemoryInst()->getOperand(1));
      auto *Base = dyn_cast<SCEVUnknown>(SE.getPointerBase(Ptr));
      MemPtr = Base->getValue();
      dbgs() << getNameOrAsOperand(MemPtr) << " is modified\n";
    }
  }
};

PreservedAnalyses REVPass::run(Function &F, FunctionAnalysisManager &AM) {
  outs() << F.getName() << "\n";
  for (auto &A : F.args()) {
    if (A.getType()->isPointerTy())
      A.addAttr(Attribute::NoAlias);
  }

  LoopInfo &LI = AM.getResult<LoopAnalysis>(F);
  ScalarEvolution &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
  DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
  BasicAAResult &AA = AM.getResult<BasicAA>(F);
  MemorySSA &MSSA = AM.getResult<MemorySSAAnalysis>(F).getMSSA();
  MSSA.ensureOptimizedUses();
  auto *Walker = MSSA.getWalker();

  LambdaV2 Lam(LI, SE, MSSA);
  Lam.translate(F);

  return PreservedAnalyses::all();
  Node *LO;
  std::vector<LevelBounds> Levels;
  struct CSRLevels CSR;
  if (LI.getTopLevelLoops().size() == 0) {
    // TODO handle memory too
    for (auto &BB : F) {
      for (auto &I : BB) {
        if (auto *Ret = dyn_cast<ReturnInst>(&I)) {
          LO = new Node(Ret);
          break; // TODO multiple values
        }
      }
    }
  } else {
//    Translate Tr(&LI, &SE, &MSSA);
//    Tr.visit(&F);
//    dbgs() << Tr;
//    return PreservedAnalyses::all();

    LoopNest LN(*LI.getTopLevelLoops()[0], SE);
    for (int Depth = LN.getNestDepth(); Depth > 0; --Depth){
      auto *L = LN.getLoopsAtDepth(Depth)[0];
      auto *IV = L->getInductionVariable(SE);
      SmallVector<std::string> Start;
      SmallVector<PHINode*> Params;
//      for (auto *BB : L->blocks()) {
//        auto *First = BB->getFirstNonPHI();
//
//        for (auto &I : *BB) {
//          switch (I.get) {
//
//          }
//        }
//      }
      
      auto *MemPhi = MSSA.getMemoryAccess(L->getHeader());
      if (MemPhi) {
        auto *V = MemPhi->getIncomingValueForBlock(L->getLoopPreheader());
        auto *MP = dyn_cast<MemoryPhi>(V);
        auto *MD = dyn_cast<MemoryUseOrDef>(V);
        if (MP)
          Start.push_back("heap." + std::to_string(MP->getID()));
        else {
          if (MSSA.isLiveOnEntryDef(MD))
            Start.push_back("heap.liveOnEntry");
          else
            Start.push_back("heap." + getNameOrAsOperand(MD->getMemoryInst()));
        }
      }

      for (auto &Phi : L->getHeader()->phis()) {
        if (&Phi != IV) {
          Start.push_back(getNameOrAsOperand(Phi.getIncomingValueForBlock(L->getLoopPreheader())));
          Params.push_back(&Phi);
        }
      }
      Params.push_back(IV);
      // generate f
      Executor E;
      std::string f = "Abs([";
      raw_string_ostream Abs(f);
      ListSeparator LS(", ");
      if (MemPhi) {
        auto *LoopVal = MemPhi->getIncomingValueForBlock(L->getLoopLatch());
        auto *MP = dyn_cast<MemoryPhi>(LoopVal);
        auto *MD = dyn_cast<MemoryUseOrDef>(LoopVal);
        if (MP)
          Abs << LS << "heap." + std::to_string(MP->getID());
        else {
          auto *MI = MD->getMemoryInst();
          Abs << LS << E.SExpr(getLoadStorePointerOperand(MI));
        }
      }
      for (auto *P : Params) {
        Abs << LS << getNameOrAsOperand(P);
      }
      f += "] ";
      if (MemPhi) {
        auto *LoopVal = MemPhi->getIncomingValueForBlock(L->getLoopLatch());
//        auto *Clob = MSSA.getWalker()->getClobberingMemoryAccess(LoopVal);
        auto *MP = dyn_cast<MemoryPhi>(LoopVal);
        auto *MD = dyn_cast<MemoryUseOrDef>(LoopVal);
        if (MP)
          f += "heap." + std::to_string(MP->getID());
        else {
          auto *MI = MD->getMemoryInst();
          f += E.SExpr(MI) + " ";
        }
      }
      for (auto *P : Params) {
        if (P == IV)
          continue;
        f += E.SExpr(P->getIncomingValueForBlock(L->getLoopLatch()));
        f += " ";
      }

      LLVM_DEBUG({
        dbgs() << L->getName() << ": \n";
        dbgs() << "fold (";
        ListSeparator LS(", ");
        for (auto &V : Start) dbgs() << LS << V;
        dbgs() << ") ";
        dbgs() << f << ")";
        auto B = L->getBounds(SE);
        dbgs() << " Range(" << getNameOrAsOperand(&B->getInitialIVValue())
               << ", " << getNameOrAsOperand(&B->getFinalIVValue()) << ")\n";
      });
    }
    return PreservedAnalyses::all();

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
    DenseMap<Value *, Tensor *> TensorMap;
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

    std::error_code EC;
    raw_fd_ostream SExpOut(AnalysisOutputPath + ".sexp", EC);
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
          emitFold(SExpOut, Loop, LiveOut, Loop->getInductionVariable(SE), RD, LevelMap,
                   TensorMap);
          continue;
        }
        // is it a map?
        if (auto *Store = dyn_cast<StoreInst>(LiveOut)) {
          emitMap(SExpOut, Loop, &LI, Store->getValueOperand(), Loop->getInductionVariable(SE), RD, LevelMap,
                  TensorMap);
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

    std::vector<Tensor *> AllTensors;
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