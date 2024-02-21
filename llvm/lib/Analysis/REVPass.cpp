//
// Created by avery on 27/06/23.
//

#include "llvm/Analysis/REVPass.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/DDG.h"
#include "llvm/Analysis/Delinearization.h"
#include "llvm/Analysis/DemandedBits.h"
#include "llvm/Analysis/IVDescriptors.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopNestAnalysis.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
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

std::string getNameOrAsOperand(const Value *V) {
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
    std::string Str = "(tensor " + Comp + TType + getNameOrAsOperand(Root);
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



  std::string toDense2() {
    std::string Output;
    raw_string_ostream OS(Output);
    OS << "ptr " << DimOrder.size() << " " << *ElemType << " ";
    OS << getNameOrAsOperand(Root);
    if (Kind != CONTIGUOUS)
      OS << ".dense";
    OS << "[";
    ListSeparator LS(", ");
    for (auto *I : Shape)
      OS << LS << *I->getType() << " " << getNameOrAsOperand(I);
    OS << "]";
    return Output;
  }

  Instruction *toDense(PHINode *OldIV, PHINode *NewIV, bool DelinearOnly = false) {
    std::vector<Value *> IdxList;
    std::vector<Type *> IdxTypes;
    std::string Name = getNameOrAsOperand(Root);
    Name = Name.substr(1, Name.size());
    if (Kind == CONTIGUOUS || DelinearOnly) {
      IdxList.push_back(Root);
      IdxTypes.push_back(Root->getType());
    } else {
      Name += ".dense";
      Argument *Arg = new Argument(
          PointerType::get(OldIV->getParent()->getParent()->getContext(), 0),
          Name);
      IdxList.push_back(Arg);
      IdxTypes.push_back(Arg->getType());
    }

    for (auto *V : Shape) {
      Value *Index = V == OldIV ? NewIV : V;
      //      Index = CastInst::CreateIntegerCast(Index,
      //      Type::getInt64Ty(OldIV->getParent()->getContext()), true);
      IdxList.push_back(Index);
      IdxTypes.push_back(Index->getType());
    }
    // generate a dense load or store from IV
    auto *FType = FunctionType::get(ElemType, IdxTypes, true);
    unsigned AddrSpace = OldIV->getParent()->getParent()->getAddressSpace();
    auto *Func =
        Function::Create(FType, OldIV->getParent()->getParent()->getLinkage(),
                         AddrSpace, "llvm.load.ptr");

    //    auto *Call = CallInst::Create(FType, Func, IdxList, Name);
    auto *Load = IntrinsicInst::Create(Func, IdxList, Name + ".elem");
    return Load;
  }
};

class Exp {
public:
  enum ExpKind {
    EK_Var,
    EK_Abs,
    EK_Apply,
    EK_Builtin,
    EK_IfThen,
    EK_Let,
    EK_Tuple,
    EK_MemLoad,
    EK_MemStore
  };
  Exp(ExpKind K) : Kind(K) {}
  virtual void print(raw_ostream &OS) const = 0;
  void dump() { print(dbgs()); }
  ExpKind getKind() const { return Kind; }

private:
  const ExpKind Kind;
};
raw_ostream &operator<<(raw_ostream &OS, Exp const &E) {
  E.print(OS);
  return OS;
}

class Var : public Exp {
  std::vector<Value *> Elems;

public:
  Var(Value *V) : Exp(EK_Var) { Elems.push_back(V); }
  Var(std::vector<Value *> &Elems) : Exp(EK_Var), Elems(Elems) {}
  Var(iterator_range<Function::arg_iterator> Args) : Exp(EK_Var) {
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
  Abs(Var *P, Exp *B) : Exp(EK_Abs), Params(P), Body(B) {}
  void print(raw_ostream &OS) const { OS << "λ" << *Params << ". " << *Body; }
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
  enum SupportedOps { Add, Mult, LT, GT, Not };
  SupportedOps Op;

  Builtin(Instruction *Op, Exp *L, Exp *R)
      : Exp(EK_Builtin), InstOp(Op), Es({L, R}) {
    makeOp();
  }
  Builtin(SupportedOps Op, Exp *E) : Exp(EK_Builtin), Op(Op), Es({E}) {}
  static Builtin *mkNot(Exp *E) { return new Builtin(Not, E); }
  void print(raw_ostream &OS) const {
    OS << "(" << op2String() << " ";
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
  IfThen(Exp *C, Exp *T, Exp *E) : Exp(EK_IfThen), C(C), Then(T), Else(E) {}
  void print(raw_ostream &OS) const {
    OS << "if " << *C << " then " << *Then << " else " << *Else;
  }
};
class Let : public Exp {
  Var *L;
  Exp *V;
  Exp *B;

public:
  Let(Var *L, Exp *V, Exp *B) : Exp(EK_Let), L(L), V(V), B(B) {}
  Let() : Exp(EK_Let), L(nullptr), V(nullptr), B(nullptr) {}
  void print(raw_ostream &OS) const {
    OS << "let " << *L << " = " << *V << " in " << *B << "\n";
  }
  void insert(Exp *E) { // TODO cache bottom ptr to make O(1) not O(n)
    if (B == nullptr) {
      B = E;
    } else if (auto *Chain = dyn_cast<Let>(B)) {
      Chain->insert(E);
    } else
      llvm_unreachable("something weird");
  }
  static bool classof(const Exp *E) { return E->getKind() == EK_Let; }
};
class Tuple : public Exp {};
class MemLoad : public Exp {
  Exp *Ptr;
  Exp *Idx;
  LoadInst *L = nullptr;

public:
  MemLoad(Exp *Ptr, Exp *Idx, LoadInst *L)
      : Exp(EK_MemLoad), Ptr(Ptr), Idx(Idx), L(L) {}
  void print(raw_ostream &OS) const { OS << *Ptr << "[" << *Idx << "]"; }
};
class MemStore : public Exp {};

// inline everything except for loads
class Inline : public InstVisitor<Inline, Exp *> {
public:
  Inline(DominatorTree &DT) : DT(DT) {}

  Exp *run(Value *V) {
    if (auto *I = dyn_cast<Instruction>(V)) {
      Exp *Result = visit(I);
      Var *Left = new Var(I);
      return new Let(Left, Result, {});
    }
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

  Exp *visitPHINode(PHINode &I) {
    if (I.getNumIncomingValues() == 1)
      return new Var(I.getOperand(0));
    auto *BB1 = I.getIncomingBlock(0);
    auto *BB2 = I.getIncomingBlock(1);
    auto *Denom = DT.findNearestCommonDominator(BB1, BB2);
    auto *Br = dyn_cast<BranchInst>(Denom->getTerminator());
    assert(Br && Br->isConditional() && "something weird");
    auto *True = Br->getSuccessor(0);
    auto *False = Br->getSuccessor(1);
    auto *Cond = Br->getCondition();
    Value *Then, *Else;
    if (DT.dominates(True, I.getIncomingBlock(0))) {
      Then = I.getIncomingValue(0);
      Else = I.getIncomingValue(1);
    } else {
      assert(DT.dominates(True, I.getIncomingBlock(1)) && "something weird");
      Else = I.getIncomingValue(0);
      Then = I.getIncomingValue(1);
    }
    IfThen(run(Cond), run(Then), run(Else));
  }

  Exp *visitInstruction(Instruction &I) { return visit(I); }

private:
  DominatorTree &DT;
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
    switch (Op.getOpcode()) {
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
  ExecutorDense(DenseMap<Value *, Tensor *> &TensorMap)
      : TensorMap(TensorMap) {}

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
  std::vector<Value *> CoordArrays;
  std::vector<Value *> PosArrays;
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
            if (*Crd != nullptr)
              return false; // no multiples allowed
            *Crd = PrevLoad;
            return true;
          } else {
            PrevLoad = L;
            Loads += 1;
          }
        }
        if (DFS(U, PrevLoad, Loads, Visited))
          return true; // only fire return when positive
      }
    }
    return *Crd != nullptr;
  };
  return DFS(Inst, nullptr, 0, {});
}

void makeLevelBounds(LoopInfo &LI, ScalarEvolution *SE,
                     std::vector<LevelBounds> &Levels) {

  DataLayout DL = SE->getDataLayout();

  for (auto *L : LI.getLoopsInPreorder()) {
    auto Bounds = L->getBounds(*SE);
    if (!Bounds.has_value())
      continue;
    auto *IndVar = L->getInductionVariable(*SE);
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

void emitFold(raw_fd_ostream &FS, Loop *L, Value *LiveOut, PHINode *Iterator,
              RecurrenceDescriptor &RD,
              DenseMap<Value *, LevelBounds> &LevelMap,
              DenseMap<Value *, Tensor *> &TensorMap) {
  std::string Total;
  Total += "(loop \"" + L->getHeader()->getName().str() + "\"\n\t";
  // Name map
  std::string Names =
      "(table (" + Val2Sexp(Iterator) + " " + Val2Sexp(Iterator, ".d") + "))";
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
  SmallPtrSet<Value *, 4> Loads;
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
  DenseExpr +=
      buildDenseExpression(LiveOut, Iterator, RD, LevelMap, TensorMap, Inputs);
  DenseExpr += ")";
  //  LLVM_DEBUG({ dbgs() << DenseExpr << "\n"; });
  Total += "(target \n\t\t" + DenseExpr + "))\n";
  LLVM_DEBUG({ dbgs() << Total << "\n"; });
  FS << Total;
}

std::string nameMap(PHINode *Iterator,
                    DenseMap<Value *, LevelBounds> &LevelMap) {
  if (LevelMap[Iterator].LevelType == COMPRESSED)
    return "(table (" + Val2Sexp(Iterator) + " " + Val2Sexp(Iterator, ".d") +
           "))";
  return "(table )";
}

std::string valMap(Value *LiveOut, LoopInfo *LI, Loop *L,
                   DenseMap<Value *, Tensor *> &TensorMap) {
  std::string ValMap = "(table ";
  Executor E;
  SmallPtrSet<Value *, 4> Loads;
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
  if (auto *Mem = getPointerOperand(Root))
    Next = skipCasts(Mem);
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
    LevelMap[*I].PosArrays.push_back(*Row);
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

bool detectDense2D(LoopInfo *LI, ScalarEvolution *SE, Value *Root, Value **A,
                   Value **Pk_1, Value **Nk, Value **Ik,
                   DenseMap<Value *, LevelBounds> &LevelMap) {
  Instruction *I, *J;
  *A = *Pk_1 = *Nk = *Ik = nullptr;

  Value *Next = nullptr;
  if (auto *Mem = getPointerOperand(Root))
    Next = skipCasts(Mem);
  else
    return false;

  if (auto *GEP = dyn_cast<GEPOperator>(Next)) {
    if (GEP->getSourceElementType()->isArrayTy() && GEP->getNumIndices() == 2) {
      *A = GEP->getPointerOperand();
      *Pk_1 = skipCasts(GEP->getOperand(1));
      *Ik = skipCasts(GEP->getOperand(2));
      return true;
    }
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

  return false;
}

bool detectDense1D(LoopInfo *LI, ScalarEvolution *SE, Value *Root, Value **x,
                   Value **Ik, DenseMap<Value *, LevelBounds> &LevelMap) {
  *x = *Ik = nullptr;

  Value *Next = nullptr;
  if (auto *Mem = getPointerOperand(Root))
    Next = skipCasts(Mem);
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

bool detectDense1D_fallback(LoopInfo *LI, ScalarEvolution *SE, Value *Root, Value **x,
                   Value **Ik, DenseMap<Value *, LevelBounds> &LevelMap) {
  *x = *Ik = nullptr;

  Value *Next = nullptr;
  if (auto *Mem = getPointerOperand(Root))
    Next = skipCasts(Mem);
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

  *Ik = LI->getLoopFor(dyn_cast<Instruction>(Next)->getParent())->getInductionVariable(*SE);

  return true;
}

bool coverAllLoads(LoopInfo *LI, ScalarEvolution *SE,
                   SmallVector<Value *> &Loads,
                   DenseMap<Value *, LevelBounds> &LevelMap,
                   SmallPtrSetImpl<Value *> &Leftover,
                   DenseMap<Value *, Tensor *> &TensorMap) {
  // 1. how the load is indexed? eg by dense or compressed level iterator
  // 2. how the load is used? eg as ptr (to index other array) or in
  // computation?
  bool Change = true;
  SmallPtrSet<Value *, 5> WorkList;
  for (auto *L : Loads)
    WorkList.insert(L);
  while (Change) {
    Change = false;
    SmallVector<Value *> ToRemove;
    for (auto *Load :
         WorkList) { // TODO figure out how to undo LevelMap mutations
      Value *Row, *Col, *Val, *I, *J;
      auto IsCSR = detectCSR(LI, Load, &Row, &Col, &Val, &I, &J, LevelMap);
      if (IsCSR) {
        auto *TensorCSR = new CSR({I, J}, Load->getType(), Val, Row, Col);
        //        CSR TensorCSR({Rows, nullptr}, Val, Row, Col);
        TensorMap[Load] = TensorCSR;
//        TensorMap[getLoadStorePointerOperand(Load)] = TensorCSR;
        // find all the memory users of the pos (row) iterator and mark them?
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

      Value *A, *Pk_1, *Nk, *Ik;
      auto IsDense2D =
          detectDense2D(LI, SE, Load, &A, &Pk_1, &Nk, &Ik, LevelMap);
      if (IsDense2D) {
        auto *D1 = LevelMap[Pk_1].UpperBound;
        auto *D2 = LevelMap[Ik].UpperBound;
        Type *Ty;
        if (auto *S = dyn_cast<StoreInst>(Load))
          Ty = S->getValueOperand()->getType();
        else
          Ty = Load->getType();
        auto *Dense2D = new Vector({Pk_1, Ik}, Ty, A);
        //        Vector Dense2D({D1, D2}, A);
        TensorMap[Load] = Dense2D;
        TensorMap[getLoadStorePointerOperand(Load)] = Dense2D;
            LLVM_DEBUG({
          dbgs() << "detected dense 2d\n";
          dbgs() << "A = " << *A << "\n";
          dbgs() << "p_{k-1} = " << *Pk_1 << "\n";
          //          dbgs() << "N_k = " << *Nk << "\n";
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
        Type *Ty;
        if (auto *S = dyn_cast<StoreInst>(Load))
          Ty = S->getValueOperand()->getType();
        else
          Ty = Load->getType();
        auto *Dense1D = new Vector({Ik}, Ty, x);
        //        Vector Dense1D({D1}, x);
        TensorMap[Load] = Dense1D;
        TensorMap[getLoadStorePointerOperand(Load)] = Dense1D;
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
}

void makeTopLevelInputs(Value *LiveOut, SmallPtrSetImpl<Value *> &Inputs) {
  if (auto *Store = dyn_cast<StoreInst>(LiveOut)) {
    Inputs.insert(Store);
    LiveOut = Store->getValueOperand();
  }
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

class Fold {
  std::vector<MemoryPhi *> MemInputs;
  std::vector<PHINode *> Inputs;
  std::vector<MemoryAccess *> MemOutputs;
  std::vector<Value *> Outputs;
  Loop *L;
  LoopInfo *LI;
  DominatorTree *DT;
  ScalarEvolution *SE;
  MemorySSA *MSSA;
  DenseMap<Value *, Tensor *> &TM;

public:
  Fold(Loop *L, LoopInfo *LI, ScalarEvolution *SE, DominatorTree *DT,
       MemorySSA *MSSA, DenseMap<Value *, Tensor *> &TM,
       std::vector<MemoryPhi *> MI, std::vector<PHINode *> I,
       std::vector<MemoryAccess *> MO, std::vector<Value *> C)
      : MemInputs(MI), Inputs(I), MemOutputs(MO), Outputs(C), L(L), LI(LI),
        DT(DT), SE(SE), MSSA(MSSA), TM(TM) {}

  Value *getChain(std::vector<Value *> &Chain) {
    Value *Out = nullptr;
    if (!Outputs.empty()) {
      auto *PN = dyn_cast<PHINode>(Outputs[0]);
      auto *Inst = dyn_cast<Instruction>(PN->getIncomingValue(0));
      //      Out = Inst;
      Out = Outputs[0];
      opChain<Instruction>(Inst, Chain);
    } else if (!MemOutputs.empty()) {
      Out = MemOutputs[0];
      opChain<MemoryAccess>(dyn_cast<MemoryAccess>(MemOutputs[0]), Chain);
    }
    return Out;
  }

  std::string arrayType(Value *I) {
    // TODO don't do reverse lookup
    for (auto &E : TM) {
      if (E.getSecond() && E.getSecond()->Root == I) {
        Tensor *T = E.getSecond();
        std::string Out;
        raw_string_ostream O(Out);
        O << "ptr " << T->DimOrder.size() << " " << *T->ElemType;
        return Out;
      }
    }
    llvm_unreachable("val doesn't exist in tensor map.");
  }

  void printParams(raw_ostream &OS, std::vector<MemoryPhi *> &MI,
                   std::vector<PHINode *> &Ins, Value *MemPtr) {
    ListSeparator LS(", ");
    for (auto *V : MI)
      OS << LS << arrayType(MemPtr) << " " << getNameOrAsOperand(MemPtr);
    for (auto *V : Ins)
      OS << LS << *V->getType() << " " << getNameOrAsOperand(V);
  }

  template <class PHITy>
  void printPhi(raw_ostream &OS, PHITy *Phi, Value *MemPtr) {
    std::string LeftName = "";
    if (auto *M = dyn_cast<MemoryPhi>(Phi))
      LeftName = getNameOrAsOperand(MemPtr) + "." + std::to_string(M->getID());
    else
      LeftName = getNameOrAsOperand(Phi);

    if (Phi->getNumIncomingValues() == 1) {
      // TODO I don't think memory phis will have this
      if (auto *M = dyn_cast<MemoryPhi>(Phi))
        llvm_unreachable("weird.");
      OS << "  " << LeftName << " = "
         << getNameOrAsOperand(Phi->getIncomingValue(0)) << "\n";
      return;
    }
    auto *BB1 = Phi->getIncomingBlock(0);
    auto *BB2 = Phi->getIncomingBlock(1);
    auto *Denom = DT->findNearestCommonDominator(BB1, BB2);
    auto *Br = dyn_cast<BranchInst>(Denom->getTerminator());
    BasicBlock *Then, *Else;
    if (DT->dominates(cast<BasicBlock>(Br->getOperand(2)), BB1)) {
      // true branch dominates BB1
      Then = BB1;
      Else = BB2;
    } else {
      Then = BB2;
      Else = BB1;
    }
    OS << "  " << LeftName << " = if " << getNameOrAsOperand(Br->getCondition())
       << " then ";
    if (auto *MP = dyn_cast<MemoryPhi>(Phi)) {
      auto MemName = getNameOrAsOperand(MemPtr);
      OS << MemName << "." << MP->getIncomingValueForBlock(Then)->getID();
      OS << " else ";
      OS << MemName << "." << MP->getIncomingValueForBlock(Else)->getID();
    } else if (auto *P = dyn_cast<PHINode>(Phi)) {
      OS << getNameOrAsOperand(P->getIncomingValueForBlock(Then));
      OS << " else ";
      OS << getNameOrAsOperand(P->getIncomingValueForBlock(Else));
    }
    OS << "\n";
  }

  void printChain(raw_ostream &OS, Value *MemPtr, std::vector<Value *> &Chain,
                  std::vector<Value *> *OrigChain) {
    for (int i = Chain.size() - 1; i >= 0; --i) {
      Value *I = Chain[i];
      if (auto *P = dyn_cast<PHINode>(I)) {
        printPhi(OS, P, MemPtr);
      } else if (auto *MP = dyn_cast<MemoryPhi>(I)) {
        printPhi(OS, MP, MemPtr);
      }
      //       else if (auto *S = dyn_cast<StoreInst>(I)) {
      //        auto *Store = S;
      //        if (OrigChain)
      //          Store = dyn_cast<StoreInst>(OrigChain->operator[](i));
      //        auto *Def = dyn_cast<MemoryDef>(MSSA->getMemoryAccess(Store));
      //        assert(Def != nullptr && "must be a def here.");
      //        OS << "  " << getNameOrAsOperand(MemPtr) << "." << Def->getID()
      //        << " = " << *I << "\n";
      //       }
      else {
        OS << *I << "\n";
      }
      //      if (auto *MA = dyn_cast<MemoryAccess>(*I)) {
      //        if (auto *MP = dyn_cast<MemoryPhi>(MA)) {
      //          auto *BB1 = MP->getIncomingBlock(0);
      //          auto *BB2 = MP->getIncomingBlock(1);
      //          auto *Denom = DT->findNearestCommonDominator(BB1, BB2);
      //          auto *Br = dyn_cast<BranchInst>(Denom->getTerminator());
      //          auto MemName = getNameOrAsOperand(MemPtr);
      //          auto LeftName = MemName + "." + std::to_string(MP->getID());
      //          OS << "  " << LeftName << " = if " <<
      //          getNameOrAsOperand(Br->getCondition()) << " then "; if (BB1 ==
      //          L->getHeader())
      //            OS << MemName;
      //          else
      //            OS << MemName << "." << MP->getIncomingValue(0)->getID();
      //          OS << " else ";
      //          if (BB2 == L->getHeader())
      //            OS << MemName;
      //          else
      //            OS << MemName << "." << MP->getIncomingValue(1)->getID();
      //          OS << "\n";
      //        } else {
      //          OS << *MA << "\n"; // TODO should never happen now?
      //        }
      //      }
    }
  }

  void printFold(raw_ostream &OS, PHINode *IV, Value *Start, Value *End,
                 Value *Out, Value *MemPtr) {
    std::string OutputName = "";
    if (auto *M = dyn_cast<MemoryAccess>(Out))
      OutputName =
          getNameOrAsOperand(MemPtr) + "." + std::to_string(M->getID());
    else
      OutputName = getNameOrAsOperand(Out);

    OS << OutputName << " = fold (";
    ListSeparator LS(", ");
    for (auto *V : MemInputs) {
      auto *Incoming = V->getIncomingValueForBlock(L->getLoopPreheader());
      OS << LS << arrayType(MemPtr) << " ";
      if (MSSA->isLiveOnEntryDef(Incoming))
        OS << getNameOrAsOperand(MemPtr);
      else if (auto *M = dyn_cast<MemoryAccess>(Incoming))
        OS << getNameOrAsOperand(MemPtr) + "." + std::to_string(M->getID());
    }
    for (auto *V : Inputs) {
      if (V == IV)
        continue;
      auto *Incoming = V->getIncomingValueForBlock(L->getLoopPreheader());
      OS << LS << *Incoming->getType() << " " << getNameOrAsOperand(Incoming);
    }
    OS << ") "
       << "%" << L->getName() << " ";
    OS << "Range(" << *Start->getType() << " " << getNameOrAsOperand(Start)
       << ", " << *End->getType() << " " << getNameOrAsOperand(End) << ")\n";
  }

  // init is generated by incoming val for all input phis
  // combiner is generated by translating the output phis/stores
  void dump(ScalarEvolution &SE, Value *MemPtr, MemorySSA &MSSA,
            DenseMap<Value *, LevelBounds> &LevelMap) {
    // TODO I really need to clean this up !!!! but make it work first.
    auto B = L->getBounds(SE);
    auto &Start = B->getInitialIVValue();
    auto &End = B->getFinalIVValue();

    std::vector<Value *> Chain;
    // collect the list of instructions that generate the output
    Value *Out = getChain(Chain);

    auto *IV = L->getInductionVariable(SE);
    LLVM_DEBUG({
      dbgs() << "%" << L->getName() << " = λ";
      printParams(dbgs(), MemInputs, Inputs, MemPtr);
      dbgs() << " .\n";

      printChain(dbgs(), MemPtr, Chain, {});
      printFold(dbgs(), IV, &Start, &End, Out, MemPtr);
    });

    PHINode *NewIV;
    if (LevelMap[L->getInductionVariable(SE)].LevelType != DENSE) {
      std::vector<Value *> DenseChain;
      // densify the above list
      Value *NewOut = mkDenseChain(Chain, DenseChain, TM, &NewIV);
      if (auto *S = dyn_cast<StoreInst>(NewOut)) {
        NewOut = Out;
      }
      Value *NewStart, *NewEnd;
      //    LLVM_DEBUG({
      dbgs() << "%" << L->getName() << ".dense = λ";
      std::vector<PHINode *> NewIns(Inputs);
      NewIns.pop_back();
      NewIns.push_back(NewIV);
      printParams(dbgs(), MemInputs, NewIns, MemPtr);
      dbgs() << " .\n";

      printChain(dbgs(), MemPtr, DenseChain, &Chain);

      LLVMContext &C = L->getHeader()->getContext();
      auto Name = getNameOrAsOperand(&End) + ".dense";
      Name = Name.substr(1, Name.size());
      NewStart = ConstantInt::get(Type::getInt32Ty(C), 0);
      auto *FType = FunctionType::get(End.getType(), {});
      auto *Func = Function::Create(
          FType, L->getHeader()->getParent()->getLinkage(), "llvm.freshvar");
      NewEnd = IntrinsicInst::Create(Func, Name);

      printFold(dbgs(), IV, NewStart, NewEnd, NewOut, MemPtr);

      for (auto *I : DenseChain)
        I->deleteValue();
    } else {
      NewIV = IV;
    }

    dbgs() << "pos: (";
    ListSeparator LS1(", ");
    for (auto *Arr : LevelMap[IV].PosArrays) {
      dbgs() << LS1 << getNameOrAsOperand(Arr) << " = "
             << getNameOrAsOperand(NewIV);
    }
    dbgs() << ")\n";

    dbgs() << "crd: (";
    ListSeparator LS2(", ");
    for (auto *Arr : LevelMap[IV].CoordArrays) {
      dbgs() << LS2 << getNameOrAsOperand(Arr) << " = "
             << getNameOrAsOperand(NewIV);
    }
    dbgs() << ")\n";

    auto ChainsInTM =
        make_filter_range(Chain, [&](Value *V) { return TM.count(V); });
    ListSeparator LS3(", ");
    dbgs() << "val: (";
    for (auto *P : ChainsInTM) {
      if (!TM[P] || TM[P]->Kind == Tensor::CONTIGUOUS)
        continue;
      dbgs() << LS3 << getNameOrAsOperand(P) << " = "
             << getNameOrAsOperand(TM[P]->Root) << ".dense.elem";
    }
    dbgs() << ")\n";

    if (NewIV != IV)
      delete NewIV;
  }

  template <typename PHITy>
  void visitPHI(PHITy *V, std::vector<Value *> &Chain) {
    const BasicBlock *Parent;
    if (auto *M = dyn_cast<MemoryPhi>(V))
      Parent = M->getBlock();
    else if (auto *P = dyn_cast<PHINode>(V))
      Parent = P->getParent();
    if (LI->isLoopHeader(Parent))
      return; // avoid cycles
    if (LI->getLoopFor(Parent)->getExitBlock() == Parent)
      return; // cut at liveouts of other loops
    Chain.push_back(V);
    if (V->getNumIncomingValues() == 1) {
      collectInsts(V->getIncomingValue(0), Chain);
      return;
    }
    assert(V->getNumIncomingValues() == 2 && "assumption violated");
    auto *In1 = V->getIncomingBlock(0);
    auto *In2 = V->getIncomingBlock(1);
    auto *Denom = DT->findNearestCommonDominator(In1, In2);
    auto *Br = dyn_cast<BranchInst>(Denom->getTerminator());
    assert(Br != nullptr && "must be a branch inst.");
    assert(Br->isConditional() && "must be conditional.");
    collectInsts<Instruction>(dyn_cast<Instruction>(Br->getCondition()), Chain);
  }

  template <class ChainTy>
  void collectInsts(ChainTy *V, std::vector<Value *> &Chain) {
    if (any_of(Chain.begin(), Chain.end(), [&](Value *E) { return V == E; }))
      return; // TODO make this O(1) instead of O(n)

    if (auto *PN = dyn_cast<PHINode>(V)) {
      visitPHI(PN, Chain);
    } else if (auto *MP = dyn_cast<MemoryPhi>(V)) {
      visitPHI(MP, Chain);
    } else {
      if (auto *I = dyn_cast<Instruction>(V)) {
        Chain.push_back(V);
        for (auto &Use : I->operands())
          collectInsts(dyn_cast<Value>(&Use), Chain);
      } else if (auto *MA = dyn_cast<MemoryUseOrDef>(V)) {
        // already checked above if it's a memory phi, so can't be here
        Chain.push_back(MA->getMemoryInst());
        for (auto &Use : MA->getMemoryInst()->operands())
          collectInsts(dyn_cast<Value>(&Use), Chain);
      }
    }
  }

  template <class ChainTy>
  void opChain(ChainTy *Root, std::vector<Value *> &Chain) {
    // collect instructions from exit val up to leaves:
    // function arguments or block args (phis in header)
    // phis elsewhere, like latch, need to be followed within the same loop,
    // including the common denom. branch inst.
    collectInsts<ChainTy>(Root, Chain);
  }

  // return the instruction to replace so that the load
  // becomes affine, or nullptr
  Instruction *indirectLoad(Value *I) {
    auto *Load = dyn_cast<LoadInst>(I);
    if (!Load)
      return nullptr;
    auto *GEP = dyn_cast<GEPOperator>(Load->getPointerOperand());
    if (!GEP)
      return nullptr;
    auto *Idx = GEP->getOperand(1);
    while (auto *Cast = dyn_cast<CastInst>(Idx))
      Idx = Cast->getOperand(0);
    return dyn_cast<LoadInst>(Idx);
  }

  Value *traverseDenseChain(Value *V, PHINode *IV, std::vector<Value *> &Chain,
                            std::vector<Value *> &DenseChain,
                            SmallPtrSetImpl<Value *> &Indirect,
                            DenseMap<Value *, Tensor *> &TensorMap) {
    if (none_of(Chain.begin(), Chain.end(), [&](Value *E) { return E == V; }))
      return V; // ignore insts not in the chain
    if (L->getInductionVariable(*SE) == V)
      return IV;
    // cut indirect loads
    if (auto *T = TensorMap[V]) {
      //        auto *N = MDNode::get(IV->getContext(),
      //        MDString::get(IV->getContext(), getNameOrAsOperand(IV)));
      //        dyn_cast<Instruction>(V)->setMetadata("as.affine", N);
      auto *Load = T->toDense(L->getInductionVariable(*SE), IV);
      return Load;
    }
    // inst or memphi?
    if (auto *I = dyn_cast<Instruction>(V)) {
      auto *NewI = I->clone();
      if (!NewI->getType()->isVoidTy()) {
        auto NewName = getNameOrAsOperand(I) + ".dense";
        NewI->setName(NewName.substr(1, NewName.size()));
      }
      for (size_t Op = 0; Op < I->getNumOperands(); ++Op) {
        NewI->setOperand(Op,
                         traverseDenseChain(I->getOperand(Op), IV, Chain,
                                            DenseChain, Indirect, TensorMap));
      }
      DenseChain.push_back(NewI);
      return NewI;
    } else if (auto *M = dyn_cast<MemoryAccess>(V)) {
      // TODO not sure right now
      dbgs() << "skipping memory access: " << *M << "\n";
      return M;
    }
    // don't clone values! like args
    return V;
  }

  Value *mkDenseChain(std::vector<Value *> &Chain,
                      std::vector<Value *> &DenseChain,
                      DenseMap<Value *, Tensor *> &TensorMap, PHINode **NewIV) {
    auto &Context = L->getHeader()->getParent()->getContext();

    *NewIV = PHINode::Create(Type::getInt64Ty(Context), 2, "iv.dense");
    SmallPtrSet<Value *, 4> IndirectLoads;
    for (auto *V : Chain)
      if (auto *Load = indirectLoad(V))
        IndirectLoads.insert(Load);
    Value *NewOut = traverseDenseChain(Chain[0], *NewIV, Chain, DenseChain,
                                       IndirectLoads, TensorMap);
    std::reverse(DenseChain.begin(), DenseChain.end());
    return NewOut;
  }
};

class Lambda {
public:

  std::string OUTS_STR;
  raw_string_ostream OUTS;

  Lambda(LoopInfo &LI, ScalarEvolution &SE, MemorySSA &MSSA,
         DenseMap<Value *, Tensor *> &TM, DenseMap<Value *, LevelBounds> &LM)
      : OUTS(OUTS_STR), LI(LI), SE(SE), MSSA(MSSA), DT(MSSA.getDomTree()), TensorMap(TM),
        LevelMap(LM) {}

  std::string arrayType(Value *I) {
    // TODO don't do reverse lookup
    std::string Out;
    raw_string_ostream O(Out);
    O << "ptr";
    for (auto &E : TensorMap) {
      if (E.getSecond() && E.getSecond()->Root == I) {
        Tensor *T = E.getSecond();
        O << " " << T->DimOrder.size() << " " << *T->ElemType;
        return Out;
      }
    }
    return Out;
//    llvm_unreachable("val doesn't exist in tensor map.");
  }

  template <class PHITy>
  BranchInst *getPhiBr(PHITy *Phi, BasicBlock **Then, BasicBlock **Else) {
    if (Phi->getNumIncomingValues() != 2)
      return nullptr;
    auto *BB1 = Phi->getIncomingBlock(0);
    auto *BB2 = Phi->getIncomingBlock(1);
    BasicBlock *CommonDenom = DT.findNearestCommonDominator(BB1, BB2);
    BranchInst *Br = dyn_cast<BranchInst>(CommonDenom->getTerminator());
    if (Br == nullptr)
      return Br;
    bool IsTrueBr = DT.dominates(cast<BasicBlock>(Br->getOperand(2)), BB1);
    IsTrueBr ? (*Then = BB1, *Else = BB2) : (*Then = BB2, *Else = BB1);
    return Br;
  }
  // a loop has a header/latch/exit blocks,
  // and series of BBs/instructions in the body
  // visit each BB in the loop body, there are
  // two possibilities:
  // (1) block is the header for a loop (subloop)
  //      then, mkFold(header, ..., latch, loop-exit)
  //      loop-exit has phis (scalar liveouts)
  //      and/or contains memory-defs with outside users
  // (2) block is part of the body
  //      emit the instructions (phis -> deduce br cond)
  //      skip branches
  template <class PHITy> void translatePhi(Loop &L, PHITy *Phi) {
    if (Phi->getNumIncomingValues() == 1) {
      OUTS << "  " << getNameOrAsOperand(Phi) << " = ";
      auto *Val = Phi->getIncomingValue(0);
      OUTS << *Phi->getType() << " " << getNameOrAsOperand(Val) << "\n";
      return;
    }
    BasicBlock *Then, *Else;
    BranchInst *Br = getPhiBr(Phi, &Then, &Else);
    auto *TrueVal = Phi->getIncomingValueForBlock(Then);
    auto *FalseVal = Phi->getIncomingValueForBlock(Else);

    std::string Target, True, False;
    if (auto *MemPhi = dyn_cast<MemoryPhi>(Phi)) {
      std::string MemName = getNameOrAsOperand(MemPtr);
      Target = MemName + "." + std::to_string(MemPhi->getID());
      auto *InputMem = MSSA.getMemoryAccess(L.getHeader());
      True = TrueVal == InputMem
                 ? MemName
                 : MemName + "." +
                       std::to_string(cast<MemoryAccess>(TrueVal)->getID());
      False = FalseVal == InputMem
                  ? MemName
                  : MemName + "." +
                        std::to_string(cast<MemoryAccess>(FalseVal)->getID());
    } else {
      Target = getNameOrAsOperand(Phi);
      True = getNameOrAsOperand(TrueVal);
      False = getNameOrAsOperand(FalseVal);
    }

    OUTS << "  " << Target << " = if ";
    if (isa<MemoryPhi>(Phi))
      OUTS << arrayType(MemPtr) << " ";
    else
      OUTS << *TrueVal->getType() << " ";
    OUTS << getNameOrAsOperand(Br->getCondition()) << " ";
    OUTS << "then " << True << " ";
    OUTS << "else " << False << "\n";
  }

  Instruction *makeDenseBodyRecursively(Loop &L,
                                        SmallVector<Instruction *> &Body,
                                        PHINode *NewIV, Instruction *I) {
    if (!L.contains(I)) {
      Body.push_back(I);
      return I;
    }
    if (auto *T = TensorMap[I]) {
      auto *NewLoad = T->toDense(L.getInductionVariable(SE), NewIV);
      Body.push_back(NewLoad);
      return NewLoad;
    }

    auto *NewI = I->clone();
    if (!NewI->getType()->isVoidTy())
      NewI->setName(getNameOrAsOperand(I).substr(1) + ".dense");
    for (size_t Op = 0; Op < I->getNumOperands(); ++Op) {
      auto *IOp = I->getOperand(Op);
      if (auto *Phi = dyn_cast<PHINode>(IOp)) {
        if (Phi == NewIV)
          NewI->setOperand(Op, NewIV);
        // skip header phis
        if (any_of(L.getHeader()->phis(), [&](auto &P) { return &P == Phi; }))
          continue;
      }
      if (auto *ToVisit = dyn_cast<Instruction>(IOp))
        NewI->setOperand(Op, makeDenseBodyRecursively(L, Body, NewIV, ToVisit));
    }
    Body.push_back(NewI);
    return NewI;
  }

  void makeDenseBody(Loop &L, PHINode *NewIV,
                     SmallVector<Instruction *> &DenseBody,
                     SmallVector<Instruction *> &LoopBody,
                     SmallVector<const MemoryAccess *> &MemDefs) {
    // TODO reverse this
    for (auto &Phi : L.getExitBlock()->phis())
      makeDenseBodyRecursively(L, DenseBody, NewIV,
                               cast<Instruction>(Phi.getIncomingValue(0)));
    for (auto *MA : MemDefs)
      if (auto *Def = dyn_cast<MemoryDef>(MA))
        makeDenseBodyRecursively(L, DenseBody, NewIV, Def->getMemoryInst());
  }

  void translateLoopBody(Loop &L, SmallVector<const MemoryAccess *> &MemDefs,
                         SmallVector<Instruction *> &LoopBody,
                         SmallVector<Instruction *> &DenseBody) {
    auto *Header = L.getHeader();
    for (BasicBlock *BB : L.getBlocks()) {
      if (LI.getLoopFor(BB) != &L)
        continue;
      // All defs are also outputs
      if (auto *Defs = MSSA.getBlockDefs(BB))
        for (const MemoryAccess &MA : *Defs) {
          if (auto *Phi = dyn_cast<MemoryPhi>(&MA)) {
            // skip memory phis unless they appear outside the header
            if (BB == Header)
              continue;
            translatePhi(L, Phi);
          }
          // are any of the MAs used outside this loop
          BasicBlock *InstBB = MA.getBlock();
          if (any_of(MA.uses(), [&](const Use &U) {
                auto *User = cast<MemoryAccess>(U.getUser());
                auto *UserBB = User->getBlock();
                if (auto *MemPhi = dyn_cast<MemoryPhi>(User))
                  UserBB = MemPhi->getIncomingBlock(U);
                return InstBB != UserBB && !L.contains(UserBB);
              })) {
            MemDefs.push_back(&MA);
          }
        }
      BasicBlock::iterator I =
          BB == Header ? BB->getFirstInsertionPt() : BB->begin();
      BasicBlock::iterator E = BB->end();
      for (; I != E; ++I) {
        if (dyn_cast<BranchInst>(&*I) || &*I == BB->getTerminator())
          continue;
        LoopBody.push_back(&*I);
        if (auto *Phi = dyn_cast<PHINode>(&*I)) {
          translatePhi(L, Phi);
        } else if (I->mayWriteToMemory()) {
          auto *Def = cast<MemoryDef>(MSSA.getMemoryAccess(&*I));
          OUTS << "  " << getNameOrAsOperand(MemPtr);
          OUTS << "." << Def->getID() << " =" << *I << "\n";
        } else if (auto *Load = dyn_cast<LoadInst>(&*I)) {
          //          if (TensorMap.contains(Load)) {
          //            auto *T = TensorMap[Load];
          //            auto *IV = L.getInductionVariable(SE);
          //            auto *Delinear = T->toDense(IV, IV, true);
          //            Delinear->setName(getNameOrAsOperand(Load).substr(1));
          //            OUTS << *Delinear << "\n";
          //            Delinear->deleteValue();
          //          } else {
          OUTS << *I << "\n";
          //          }
        }
        //        else if (auto *GEP = dyn_cast<GEPOperator>(&*I)) {
        //          if (TensorMap.contains(GEP)) {
        //            auto *T = TensorMap[GEP];
        //            std::vector<Value*> Indices;
        //            auto &Ctx = L.getHeader()->getContext();
        //            for (auto *V : T->Shape) {
        //              auto *C = ZExtInst::CreateIntegerCast(V, Type::getInt64Ty(Ctx), true, "cast." + getNameOrAsOperand(V)); Indices.push_back(C);
        //            }
        //            ArrayType::get(GEP->getResultElementType(), )
        //            auto *NewGep = GetElementPtrInst::Create(
        //                GEP->getResultElementType(),
        //                GEP->getPointerOperand(),
        //                Indices, getNameOrAsOperand(GEP));
        //            OUTS << *NewGep << "\n";
        //            NewGep->deleteValue();
        //            for (auto *V : Indices) V->deleteValue();
        //          } else {
        //            OUTS << *I << "\n";
        //          }
        //        }
        else {
          OUTS << *I << "\n";
        }
      }
    }
    // now loopbody has all the instructions in the loop body
    // memdef has all the defining mem access, basically we
    // only need this for writing the output vals

    // we only need the instructions related to outputs
    // vals in MemDef + exit block phis

  }

  void translateLoop(Loop &L) {
    // translate header
    BasicBlock *Header = L.getHeader();
    OUTS << "%" << Header->getName() << " = λ ";
    PHINode *IV = L.getInductionVariable(SE);
    auto NonIVs =
        make_filter_range(Header->phis(), [&](PHINode &P) { return &P != IV; });
    ListSeparator LS(", ");
    if (MemoryPhi *BlockPhi = MSSA.getMemoryAccess(Header))
      OUTS << LS << arrayType(MemPtr) << " "
             << getNameOrAsOperand(MemPtr); // << "." << BlockPhi->getID();
    for (auto &P : NonIVs)
      OUTS << LS << *P.getType() << " " << getNameOrAsOperand(&P);
    OUTS << LS << *IV->getType() << " " << getNameOrAsOperand(IV) << " .\n";

    // translate loop body
    SmallVector<const MemoryAccess *> MemDefs;
    SmallVector<Instruction *> LoopBody;
    SmallVector<Instruction *> DenseBody;
    translateLoopBody(L, MemDefs, LoopBody, DenseBody);

    OUTS << "(";
    LS = ListSeparator(", ");
    for (auto &P : L.getExitBlock()->phis())
      OUTS << LS << getNameOrAsOperand(P.getIncomingValue(0));
    for (auto *D : MemDefs)
      OUTS << LS << getNameOrAsOperand(MemPtr) << "." << D->getID();
    OUTS << ") = fold (";
    LS = ListSeparator(", ");
    if (MemoryPhi *BlockPhi = MSSA.getMemoryAccess(Header)) {
      OUTS << LS << arrayType(MemPtr) << " " << getNameOrAsOperand(MemPtr);
      auto *Incoming = BlockPhi->getIncomingValueForBlock(L.getLoopPreheader());
      bool IsInLoopHeader = false;
      if (auto *Lp = LI.getLoopFor(Incoming->getBlock()))
        IsInLoopHeader = Lp->getHeader() == Incoming->getBlock();
      if (!MSSA.isLiveOnEntryDef(Incoming) && !IsInLoopHeader)
        OUTS << "." << Incoming->getID();
    }
    for (auto &P : NonIVs) {
      auto *InitialArg = P.getIncomingValueForBlock(L.getLoopPreheader());
      OUTS << LS << *InitialArg->getType() << " " << getNameOrAsOperand(InitialArg);
    }
    OUTS << ") ";
    OUTS << "%" << Header->getName() << " ";
    auto Bounds = L.getBounds(SE);
    auto *Start = &Bounds->getInitialIVValue();
    auto *End = &Bounds->getFinalIVValue();
    OUTS << "Range(" << *Start->getType() << " " << getNameOrAsOperand(Start)
           << ", " << *End->getType() << " " << getNameOrAsOperand(End)
           << ")\n";

    // emit dense


    auto &Context = L.getHeader()->getParent()->getContext();
    auto *NewIV = PHINode::Create(Type::getInt64Ty(Context), 2, IV->getName() + ".dense");

    DenseMap<Value *, Value *> DensifiedLoads;
    std::vector<Instruction *> DenseOuts;
    if (LevelMap[IV].LevelType != DENSE) {
      LS = ListSeparator(", ");
      OUTS << "%" << L.getName() << ".dense = λ ";

      if (MemoryPhi *BlockPhi = MSSA.getMemoryAccess(Header))
        OUTS << LS << arrayType(MemPtr) << " " << getNameOrAsOperand(MemPtr);

      for (auto &P : NonIVs)
        OUTS << LS << *P.getType() << " " << getNameOrAsOperand(&P);

      OUTS << LS << *NewIV->getType() << " " << getNameOrAsOperand(NewIV)
           << " .\n";

      for (auto *I : LoopBody) {
        if (!isa<LoadInst>(I) && !isa<StoreInst>(I))
          continue;

        if (TensorMap.contains(I)) {
          auto *T = TensorMap[I];
          //        auto *Delinear = T->toDense(IV, IV, true);
          //        Delinear->setName(getNameOrAsOperand(I).substr(1));
          //        OUTS << *Delinear << "\n";
          //        Delinear->deleteValue();
          if (auto *Store = dyn_cast<StoreInst>(I)) {
            auto *Def = cast<MemoryDef>(MSSA.getMemoryAccess(Store));
            OUTS << getNameOrAsOperand(MemPtr);
            OUTS << "." << Def->getID() << " = store ";
            OUTS << T->toDense2() << ", ";
            OUTS << *Store->getValueOperand()->getType() << " "
                 << getNameOrAsOperand(Store->getValueOperand()) << "\n";
          } else {
            auto *NewLoad = T->toDense(IV, NewIV);
            //          OUTS << getNameOrAsOperand(I) << " = load ";
            OUTS << *NewLoad << "\n";
            DensifiedLoads[I] = NewLoad;
          }
        }
      }

      // print liveout
      for (auto &P : L.getExitBlock()->phis()) {
        auto *NewOut = dyn_cast<Instruction>(P.getIncomingValue(0))->clone();
        NewOut->setName(getNameOrAsOperand(P.getIncomingValue(0)).substr(1) +
                        ".dense");
        for (int i = 0; i < NewOut->getNumOperands(); ++i) {
          auto *Op = NewOut->getOperand(i);
          if (DensifiedLoads.contains(Op))
            NewOut->setOperand(i, DensifiedLoads[Op]);
        }
        OUTS << *NewOut << "\n";
        DenseOuts.push_back(NewOut);
      }

      LS = ListSeparator(", ");
      OUTS << "(";
      for (auto *I : DenseOuts)
        OUTS << LS << getNameOrAsOperand(I);
      OUTS << ") = fold (";
      LS = ListSeparator(", ");
      if (MemoryPhi *BlockPhi = MSSA.getMemoryAccess(Header)) {
        OUTS << LS << arrayType(MemPtr) << " " << getNameOrAsOperand(MemPtr);
        auto *Incoming =
            BlockPhi->getIncomingValueForBlock(L.getLoopPreheader());
        bool IsInLoopHeader = false;
        if (auto *Lp = LI.getLoopFor(Incoming->getBlock()))
          IsInLoopHeader = Lp->getHeader() == Incoming->getBlock();
        if (!MSSA.isLiveOnEntryDef(Incoming) && !IsInLoopHeader)
          OUTS << "." << Incoming->getID();
      }
      for (auto &P : NonIVs) {
        auto *InitialArg = P.getIncomingValueForBlock(L.getLoopPreheader());
        OUTS << LS << *InitialArg->getType() << " "
             << getNameOrAsOperand(InitialArg);
      }

      OUTS << ") %" << L.getName() << " Range(";
      OUTS << *ConstantInt::get(Type::getInt64Ty(Context), 0) << ", ";
      OUTS << *End->getType() << " " << getNameOrAsOperand(End) << ".dense)\n";
    }

    OUTS << "pos: (";
    ListSeparator LS1(", ");
    for (auto *Arr : LevelMap[IV].PosArrays) {
      OUTS << LS1 << getNameOrAsOperand(Arr) << " = "
           << *NewIV->getType() << " " << getNameOrAsOperand(NewIV);
    }
    OUTS << ")\n";
    OUTS << "crd: (";
    ListSeparator LS2(", ");
    for (auto *Arr : LevelMap[IV].CoordArrays) {
      OUTS << LS2 << getNameOrAsOperand(Arr) << " = "
           << *NewIV->getType() << " " << getNameOrAsOperand(NewIV);
    }
    OUTS << ")\n";
    auto ChainsInTM =
        make_filter_range(LoopBody, [&](Value *V) { return TensorMap.count(V); });
    ListSeparator LS3(", ");
    OUTS << "val: (";
    for (auto *P : ChainsInTM) {
      if (!TensorMap[P] || TensorMap[P]->Kind == Tensor::CONTIGUOUS)
        continue;
      OUTS << LS3 << getNameOrAsOperand(P) << " = "
           << *TensorMap[P]->ElemType << " " << getNameOrAsOperand(TensorMap[P]->Root) << ".dense.elem";
    }
    OUTS << ")\n";

    for (auto *V : reverse(DenseBody))
      V->deleteValue();
    for (auto *I : DenseOuts)
      I->deleteValue();
    for (auto &E : DensifiedLoads)
      E.second->deleteValue();
    if (NewIV != IV)
      delete NewIV;
  }
  void translateLoopsRecursively(Loop &L) {
    for (Loop *SubLoop : L.getSubLoops())
      translateLoopsRecursively(*SubLoop);
    translateLoop(L);
  }
  void translateAllLoops(Function &F) {
    analyzeMemory(&F);
    for (const auto &L : LI)
      translateLoopsRecursively(*L);
  }

  void translate(Function &F, DenseMap<Value *, LevelBounds> &LevelMap) {
    analyzeMemory(&F);

    for (auto *TopLoop : LI.getTopLevelLoops()) {
      LoopNest LN(*TopLoop, SE);
      for (auto *Loop : LN.getLoops()) {
        auto *Header = Loop->getHeader();
        auto *Exit = Loop->getExitBlock();
        auto *Latch = Loop->getLoopLatch();
        auto *IV = Loop->getInductionVariable(SE);
        std::vector<MemoryAccess *> MemOutputs;
        std::vector<Value *> Outputs;
        if (MSSA.getBlockDefs(Latch))
          MemOutputs.push_back(
              const_cast<MemoryAccess *>(&*MSSA.getBlockDefs(Latch)->rbegin()));
        else if (auto *P =
                     dyn_cast_or_null<MemoryPhi>(MSSA.getMemoryAccess(Latch)))
          MemOutputs.push_back(P);

        for (auto &P : Exit->phis())
          Outputs.push_back(&P);
        // memory
        // a phi in the latch means the loop body is somehow modifiying memory
        // (might be in a subloop)

        std::vector<MemoryPhi *> MemInputs;
        std::vector<PHINode *> Inputs;
        if (auto *P = MSSA.getMemoryAccess(Header))
          MemInputs.push_back(P);
        for (auto &P : Header->phis()) {
          if (&P == IV)
            continue;
          Inputs.push_back(&P);
        }
        Inputs.push_back(IV);

        Fold Fl(Loop, &LI, &SE, &DT, &MSSA, TensorMap, MemInputs, Inputs,
                MemOutputs, Outputs);
        Fl.dump(SE, MemPtr, MSSA, LevelMap);
      }
    }
  }

private:
  LoopInfo &LI;
  ScalarEvolution &SE;
  MemorySSA &MSSA;
  const MemoryDef *MemInst = nullptr;
  Value *MemPtr = nullptr;
  DominatorTree &DT;
  DenseMap<Value *, Tensor *> &TensorMap;
  DenseMap<Value *, LevelBounds> &LevelMap;

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
      LLVM_DEBUG(dbgs() << getNameOrAsOperand(MemPtr) << " is modified\n");
    }
  }
};

Value *findLiveOut(const Loop *L, LoopInfo &LI) {
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
      auto *ParentLoop = LI.getLoopFor(I.getParent());
      if (ParentLoop != L)
        break;
      if (isa<StoreInst>(&I) || I.mayWriteToMemory())
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


AnalysisKey REVPass::Key;

REVInfo REVPass::run(Function &F, FunctionAnalysisManager &AM) {
  //  outs() << F.getName() << "\n";
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

  //  LoopNest LN(*LI.getTopLevelLoops()[0], SE);
  std::vector<LevelBounds> Levels;
  makeLevelBounds(LI, &SE, Levels);
  DenseMap<Value *, LevelBounds> LevelMap;
  for (auto &Level : Levels)
    LevelMap[Level.Iterator] = Level;

  // get all liveouts
  DenseMap<Loop *, Value *> LiveOutMap;

  DenseMap<Loop *, SmallPtrSet<Value *, 5>> Loop2Loads;
  for (auto *L : LI.getLoopsInPreorder()) {
    // collect live out (store or scalar live-out)
    Value *LiveOut = findLiveOut(L, LI);
    if (LiveOut == nullptr) {
      LLVM_DEBUG(dbgs() << L->getName() << " has no liveouts.\n");
      continue;
    }
    LLVM_DEBUG(dbgs() << L->getName() << " live out = " << *LiveOut << "\n");
    LiveOutMap[L] = LiveOut;
    SmallPtrSet<Value *, 5> TopLevelInputs;
    makeTopLevelInputs(LiveOut, TopLevelInputs);
    Loop2Loads[L] = TopLevelInputs;
  }

  SmallVector<Value *> TopLevelLoads;
  for (auto &E : Loop2Loads) {
    for (auto *Input : E.second)
      if (isa<LoadInst>(Input) || isa<StoreInst>(Input))
        TopLevelLoads.push_back(Input);
  }

  LLVM_DEBUG({
    dbgs() << "Top level loads ------------\n";
    for (auto *In : TopLevelLoads)
      dbgs() << *In << "\n";
    dbgs() << "----------------------------\n";
  });

  SmallPtrSet<Value *, 5> Leftover;
  DenseMap<Value *, Tensor *> TensorMap;
  auto AllCovered =
      coverAllLoads(&LI, &SE, TopLevelLoads, LevelMap, Leftover, TensorMap);
  // TODO change this later, but right now the fold assumes at least some loads
  if (TopLevelLoads.size() == 0)
    return {};
  LLVM_DEBUG({
    if (AllCovered)
      dbgs() << "all loads covered.\n";
    else {
      dbgs() << "remaining loads:\n";
      for (auto *L : Leftover)
        dbgs() << *L << "\n";
    }
  });

  if (!Leftover.empty() && TensorMap.empty()) {
    LLVM_DEBUG(dbgs() << "no sparse formats found, fall back to heaplet mode.\n");
    for (auto *L : Leftover) {
      Value *x, *Ik;
      bool IsHeaplet = detectDense1D_fallback(&LI, &SE, L, &x, &Ik, LevelMap);
      if (IsHeaplet) {
        Type *Ty;
        if (auto *S = dyn_cast<StoreInst>(L))
          Ty = S->getValueOperand()->getType();
        else
          Ty = L->getType();
        auto *Dense1D = new Vector({Ik}, Ty, x);
        TensorMap[L] = Dense1D;
        TensorMap[getLoadStorePointerOperand(L)] = Dense1D;
        LLVM_DEBUG({
          dbgs() << "detected dense 1d\n";
          dbgs() << "x = " << *x << "\n";
          dbgs() << "i_k = " << *Ik << "\n";
          dbgs() << *Dense1D << "\n";
        });
      }
    }
  }

//  if (!Leftover.empty())
//    return PreservedAnalyses::all();

  Lambda Lam(LI, SE, MSSA, TensorMap, LevelMap);
  //  Lam.translate(F, LevelMap);
  Lam.translateAllLoops(F);

  LLVM_DEBUG({
    dbgs() << "REV Start\n";
    dbgs() << Lam.OUTS_STR;
    dbgs() << "REV End\n";
  });

  return {Lam.OUTS_STR};
}

PreservedAnalyses REVPrinterPass::run(Function &F,
                                       FunctionAnalysisManager &AM) {
  auto &Res = AM.getResult<REVPass>(F);
  OS << "REV Start\n" << Res.OutStr << "REV End\n";
  return PreservedAnalyses::all();
}