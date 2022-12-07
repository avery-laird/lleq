#include "llvm/Analysis/RevAnalysis.h"
#include "z3++.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/DemandedBits.h"
#include "llvm/Analysis/IVDescriptors.h"
#include "llvm/Analysis/LoopAccessAnalysis.h"
#include "llvm/Analysis/LoopNestAnalysis.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/raw_ostream.h"
#include <chrono>
#include <cvc5/cvc5.h>
#include <fstream>
#include "llvm/IR/InstVisitor.h"
#include "llvm/Analysis/Delinearization.h"

#define DEBUG_TYPE "rev-analysis"

using namespace std::chrono;

using namespace llvm;
using namespace z3;
using namespace cvc5;

bool RevAnalysisPass::canSupportPhiInstrs(Loop *TheLoop, LoopInfo *LI,
                                          DemandedBits *DB, AssumptionCache *AC,
                                          DominatorTree *DT,
                                          ScalarEvolution *SE) {

  BasicBlock *Header = TheLoop->getHeader();
  for (PHINode &Phi : Header->phis()) {
    RecurrenceDescriptor RedDes;
    if (RecurrenceDescriptor::isReductionPHI(&Phi, TheLoop, RedDes, DB, AC, DT))
      continue;
    if (TheLoop->getInductionVariable(*SE) == (&Phi))
      continue;
    LLVM_DEBUG(dbgs() << "Found Unsupported Phi Instruction: " << Phi << "\n");
    return false;
  }
  return true;
}

void RevAnalysisPass::AnalyzeLoopBounds(Loop *L, Value *LowerBound,
                                        Value *UpperBound,
                                        ScalarEvolution *SE) {

  const SCEV *LHS = SE->getSCEV(LowerBound);
  const SCEV *RHS = SE->getSCEV(UpperBound);
  const SCEV *Res = SE->getMinusSCEV(LHS, RHS);
  //  if (auto *S = dyn_cast<SCEVAddRecExpr>(Res)) {
  //    LLVM_DEBUG(
  //        dbgs() << "The difference between lower and upper bound of loop is:
  //        "
  //               << *Res << "\n");
  //    if (S->isAffine()) {
  //      LoopForm[L] = LoopLevelFormat::Dense;
  //      return;
  //    }
  //  }
  // ADD Code to Detect Res is Loop Invariant (CSR: 0=>n, COO: 0=>nnz)
  // =>Dense
  if (SE->isLoopInvariant(Res, L)) {
    LLVM_DEBUG(dbgs() << "Bound " << *Res << "\n");
    LoopForm[L] = LoopLevelFormat::Dense;
    return;
  }
  if (auto *C = dyn_cast<SCEVConstant>(Res)) {
    LLVM_DEBUG(dbgs() << "Bound " << *C << "\n");
    LoopForm[L] = LoopLevelFormat::Dense;
    return;
  }

  // Detect Compressed Form: RowPtr[i] ==> RowPtr[i+1]
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
      const SCEV *HighIndex = SE->getSCEV(HighGEP->getOperand(1));
      const SCEV *OffsetIndex = SE->getMinusSCEV(HighIndex, LowIndex);
      while (auto *PCast = dyn_cast<BitCastInst>(LowPtrBase))
        LowPtrBase = PCast->getOperand(0);
      while (auto *PCast = dyn_cast<BitCastInst>(HighPtrBase))
        HighPtrBase = PCast->getOperand(0);
      if (LowPtrBase == HighPtrBase) {
        if (auto *C = dyn_cast<SCEVConstant>(OffsetIndex)) {
          LLVM_DEBUG(dbgs() << "offset of loop bounds is : " << *(C->getValue())
                            << "\n");
          LoopForm[L] = LoopLevelFormat::Compressed;
          return;
          //        dbgs() << "LowIdx: " << *(SE->getMinusSCEV(HighIndex,
          //        LowIndex)) << "\n"; dbgs() << "return: " << *(C->getValue())
          //        << "\n";
        }
      }
    }
  }

  //  if (SE->getSCEV(LowerBound))

  LoopForm[L] = LoopLevelFormat::Other;
  return;
}

void RevAnalysisPass::AnalyzeLoopStatements(LoopNest *LN, ScalarEvolution *SE) {

}

bool RevAnalysisPass::LegalityAnalysis(Loop *TheLoop, LoopInfo *LI,
                                       ScalarEvolution *SE) {

  if (TheLoop->getSubLoops().size() > 1) {
    LLVM_DEBUG(dbgs() << "there are multiple children loops"
                      << "\n");
    return false;
  }

  LoopNest LN(*TheLoop, *SE);
  unsigned LD = LN.getNestDepth();
  LLVM_DEBUG(dbgs() << "Depth is " << LD << "\n");

  if (LD > 2) {
    LLVM_DEBUG(dbgs() << "not support loop nests with depth > 2"
                      << "\n");
    return false;
  }

  if (!LN.areAllLoopsSimplifyForm()) {
    LLVM_DEBUG(dbgs() << "not all loops are simplified "
                      << "\n");
    return false;
  }

  for (unsigned I = LD; I > 0; I--) {
    LoopVectorTy LoopsAtDepth = LN.getLoopsAtDepth(I);
    if (LoopsAtDepth.size() > 1) {
      LLVM_DEBUG(dbgs() << "multiple loops at loop depth " << I << "\n");
      return false;
    }
  }

  for (unsigned I = LD; I > 0; I--) {
    LoopVectorTy LoopsAtDepth = LN.getLoopsAtDepth(I);
    assert(LoopsAtDepth.size() == 1 &&
           "there are more than one loop at one depth");
    Loop *L = LoopsAtDepth[0];
    Optional<Loop::LoopBounds> Bounds = L->getBounds(*SE);

    Value &LowerBound = Bounds->getInitialIVValue();
    Value &UpperBound = Bounds->getFinalIVValue();
    AnalyzeLoopBounds(L, &LowerBound, &UpperBound, SE);
    // Analyze the loop bound to obtain the property of loop at each level
  }

  for (unsigned I = 1; I <= LD; I++) {
    LoopVectorTy LoopsAtDepth = LN.getLoopsAtDepth(I);
    Loop *L = LoopsAtDepth[0];
    LLVM_DEBUG(dbgs() << "Loop Form: " << LoopForm[L] << "\n");
    if (LoopForm[L] == LoopLevelFormat::Other) {
      LLVM_DEBUG(dbgs() << "LLNA: detect the unsupported loop \n");
      return false;
    }
  }

  // The code below guarantees the loop nest only has one live-out.
  unsigned LoopIdx = 1;
  for (; LoopIdx < LD; LoopIdx++) {
    LoopVectorTy LoopsAtDepth = LN.getLoopsAtDepth(LoopIdx);
    Loop *L = LoopsAtDepth[0];
    Loop *NextL = L->getSubLoops().front();
    if (!LN.arePerfectlyNested(*L, *NextL, *SE))
      break;
  }

  Loop *CurrentLoop = LN.getLoopsAtDepth(LoopIdx)[0];
  SmallPtrSet<Value *, 16> WorkList;
  for (auto *BB : CurrentLoop->getBlocks()) {
    if (LoopIdx < LD) {
      Loop *NextL = CurrentLoop->getSubLoops().front();
      if (NextL->contains(BB))
        continue;
    }
    for (auto &I : *BB) {
      if (isa<StoreInst>(&I)) {
        LLVM_DEBUG(dbgs() << "Collect Store Instruction " << I << "\n");
        WorkList.insert(&I);
      }
    }
  }

  if (WorkList.size() > 2)
    return false;

  SmallVector<BasicBlock *> ExitBlocks;
  TheLoop->getExitBlocks(ExitBlocks);
  for (auto *BB : ExitBlocks)
    for (auto &I : *BB) {
      if (BB->getTerminator() == &I)
        break;
      PHINode *Phi = dyn_cast<PHINode>(&I);
      assert(Phi && Phi->getNumIncomingValues() == 1 &&
             "loop should be in LCSSA");
      WorkList.insert(Phi->getIncomingValue(0));
    }

  if (WorkList.size() > 2)
    return false;

  // todo: check phi instructions and exclude the loops which we don't support

  return true;
}

static z3::sort CVCSort2Z3Sort(const Sort &s, context &c) {
  if (s.isArray()) {
    return c.array_sort(CVCSort2Z3Sort(s.getArrayIndexSort(), c), CVCSort2Z3Sort(s.getArrayElementSort(), c));
  }
  if (s.isInteger()) {
    return c.int_sort();
  }
  if (s.isFloatingPoint()) {
    return c.fpa_sort(s.getFloatingPointExponentSize(), s.getFloatingPointSignificandSize());
  }
  if (s.isFunction()) {

  }
  llvm_unreachable("unsupported sort");
}

class Z3Mapping {
public:
  context &c;
  expr_vector Z3Symbols;
  func_decl_vector Z3Functions;
  std::map<std::string, int> SMapping;
  std::map<std::string, int> FMapping;
  Z3Mapping(context &c) : c(c), Z3Symbols(c), Z3Functions(c) {}
  expr_vector &symbols() { return Z3Symbols; }
  func_decl_vector &functions() { return Z3Functions; }
  void MakeMaps() {
    for (int i=0; i < Z3Symbols.size(); ++i)
      SMapping[Z3Symbols[i].to_string()] = i;
    for (int i=0; i < Z3Functions.size(); ++i)
      FMapping[Z3Functions[i].name().str()] = i;
  }
  size_t count_sym(std::string s) { return SMapping.count(s); }
  size_t count_f(std::string s) { return FMapping.count(s); }
  expr get_sym(std::string s) { return Z3Symbols[SMapping[s]]; }
  func_decl get_f(std::string s) { return Z3Functions[FMapping[s]]; }
};
// TODO: VERY MESSY BAD HACK!! this must be fixed FIRST once the demo is done
static expr CVC2Z3(Z3Mapping &Mapping, context &c, const Term &InputTerm) {
  auto Children = InputTerm.getNumChildren();
  if (Children == 0) {
    if (InputTerm.hasSymbol()) {
      if (Mapping.count_sym(InputTerm.toString()))
        return Mapping.get_sym(InputTerm.toString());
      expr constant =  c.constant(InputTerm.getSymbol().c_str(),
                        CVCSort2Z3Sort(InputTerm.getSort(), c));
      LLVM_DEBUG(dbgs() << "CVC2Z3: add symbol " << InputTerm.getSymbol() << " to map\n");
      Mapping.symbols().push_back(constant);
      return Mapping.symbols().back();
    }
    if (InputTerm.isFloatingPointValue()) {
      std::bitset<64> fpval (std::get<2>(InputTerm.getFloatingPointValue()).getBitVectorValue());
      return c.fpa_val((double)fpval.to_ullong());
    }
    if (InputTerm.isIntegerValue()) {
      return c.int_val(InputTerm.getInt64Value());
    }
    if (InputTerm.isRoundingModeValue()) {
      return c.fpa_rounding_mode();
    }
  }
  // check root
  if (!InputTerm.hasOp())
    llvm_unreachable("the node needs an op");
  expr_vector Z3Children(c);
  // need to handle APPLY_UF specially
  bool Skip = InputTerm.getOp().getKind() == APPLY_UF;
  for (auto E : InputTerm) {
    if (Skip) {
      Skip = false;
      continue;
    }
    Z3Children.push_back(CVC2Z3(Mapping, c, E));
  }
  switch (InputTerm.getOp().getKind()) {
  case APPLY_UF:
      // find definition
      if (!Mapping.count_f(InputTerm[0].getSymbol()))
        llvm_unreachable("must contain the definition");
      return Mapping.get_f(InputTerm[0].getSymbol())(Z3Children);
    break;
  case ITE:
    // three children, if - then - else
    return ite(Z3Children[0], Z3Children[1], Z3Children[2]);
  case LT:
    return Z3Children[0] < Z3Children[1];
  case SUB:
    return Z3Children[0] - Z3Children[1];
  case FLOATINGPOINT_ADD:
    return Z3Children[1] + Z3Children[2];
  case ADD:
    return Z3Children[0] + Z3Children[1];
  case SELECT:
    return Z3Children[0][Z3Children[1]];
  case FLOATINGPOINT_MULT:
    return Z3Children[1] * Z3Children[2];
  case MULT:
    return Z3Children[0] * Z3Children[1];
  case STORE:
    return store(Z3Children[0], Z3Children[1], Z3Children[2]);
  default:
    llvm_unreachable("unhandled node kind");
  }
}

class LiveInOut {
public:
  SmallPtrSet<Value *, 4> LiveIn;
  SmallPtrSet<Value *, 4> LiveOut;
  Loop *L;
  LiveInOut(Loop *L) : L(L) {}

  void CollectLiveInOut() {
    SmallPtrSet<Instruction *, 16> WorkList;
    for (auto *BB : L->getBlocks()) {
      for (auto &I : *BB) {
        WorkList.insert(&I);
        if (isa<StoreInst>(I))
          LiveOut.insert(&I);
      }
    }

    //    while (true) {
    //      auto Elems = WorkList.size();
    //      SmallPtrSet<Instruction *, 4> NewElems;
    //      for (auto *I : WorkList) {
    //        for (auto *User : I->users()) {
    //          NewElems.insert(dyn_cast<Instruction>(User));
    //        }
    //      }
    //      WorkList.insert(NewElems.begin(), NewElems.end());
    //      if (Elems == WorkList.size())
    //        break;
    //    }
    // assume loop is LCSSA and just look at the exit block
    SmallVector<BasicBlock *> ExitBlocks;
    L->getExitBlocks(ExitBlocks);
    for (auto *BB : ExitBlocks)
      for (auto &I : *BB) {
        if (BB->getTerminator() == &I)
          break;
        PHINode *Phi = dyn_cast<PHINode>(&I);
        assert(Phi && Phi->getNumIncomingValues() == 1 &&
               "loop should be in LCSSA");
        LiveOut.insert(Phi->getIncomingValue(0));
      }

    for (auto *I : WorkList) {
      if (!L->contains(I))
        LiveOut.insert(I);
    }
  }
};

class LoopAnnotations {
public:
  DenseMap<Loop *, SmallVector<std::string>> Loop2Inv;
  SmallVector<std::string> Postcondition;
};

class Z3Converter {
public:
  DenseMap<Value *, expr> Value2Z3;
  std::vector<std::pair<Value *, expr>> Allocated;
  context *c;
  Z3Converter(context *c) : c(c){};

  z3::sort type_to_sort(Type *T) {
    if (T->getTypeID() == Type::TypeID::IntegerTyID)
      return c->int_sort();
    if (T->getTypeID() == Type::TypeID::DoubleTyID)
      return c->real_sort();
  }

  expr to_Z3(Value *V) {
    if (auto *Const = dyn_cast<Constant>(V)) {
      switch (Const->getType()->getTypeID()) {
      case Type::TypeID::IntegerTyID:
        return c->int_val(dyn_cast<ConstantInt>(V)->getSExtValue());
        break;
      default:
        assert(0 && "unsupported constant type");
        break;
      }
    } else if (auto *Load = dyn_cast<LoadInst>(V)) {
      return to_Z3(getLoadStorePointerOperand(V));
    } else if (auto *GEP = dyn_cast<GEPOperator>(V)) {
      assert(GEP->getNumIndices() == 1);
      z3::sort asort = c->array_sort(type_to_sort(GEP->getSourceElementType()),
                                     type_to_sort(GEP->getResultElementType()));
      return c->constant(GEP->getPointerOperand()->getName().data(),
                         asort)[to_Z3(GEP->getOperand(1))];
    } else if (auto *Cast = dyn_cast<CastInst>(V)) {
      return to_Z3(Cast->getOperand(0));
    } else if (auto *Phi = dyn_cast<PHINode>(V)) {
      for (auto &pair : Allocated)
        if (pair.first == Phi)
          return pair.second;
      auto Tmp =
          c->constant(Phi->getName().data(), type_to_sort(Phi->getType()));
      Allocated.push_back({Phi, Tmp});
      return Tmp;
    } else if (auto *BinOp = dyn_cast<BinaryOperator>(V)) {
      switch (BinOp->getOpcode()) {
      case BinaryOperator::BinaryOps::Add:
        return to_Z3(BinOp->getOperand(0)) + to_Z3(BinOp->getOperand(1));
      default:
        assert(0 && "unsupported binop type.");
        break;
      }
    } else if (auto *Arg = dyn_cast<Argument>(V)) {
      for (auto &pair : Allocated)
        if (pair.first == Arg)
          return pair.second;
      auto Tmp =
          c->constant(Arg->getName().data(), type_to_sort(Arg->getType()));
      Allocated.push_back({Arg, Tmp});
      return Tmp;
    }

    return c->bool_val(true);
  }
};

static expr GetPostCondition() {}

static void GetLiveIns(Loop *L, SmallPtrSet<Value *, 4> &LiveIns) {
  for (auto *BB : L->getBlocks()) {
    for (auto &I : *BB) {
      for (auto &O : I.operands()) {
        // store the whole instruction and not just the operand so
        // that the type information is known (for example loads
        // and GEP on opaque pointers) https://llvm.org/docs/OpaquePointers.html
        if (auto *Inst = dyn_cast<Instruction>(&O))
          if (!L->contains(Inst))
            LiveIns.insert(&I);
        if (auto *Arg = dyn_cast<Argument>(&O))
          LiveIns.insert(&I);
      }
    }
  }

  LLVM_DEBUG(dbgs() << "Found " << LiveIns.size() << " live ins:\n");
  for (auto *V : LiveIns) {
    LLVM_DEBUG(dbgs() << *V << "\n");
  }
}

static void GetLiveOuts(Loop *L, SmallPtrSet<Value *, 4> &LiveOuts) {
  SmallVector<BasicBlock *> ExitBlocks;
  L->getExitBlocks(ExitBlocks);
  for (auto *BB : ExitBlocks)
    for (auto &I : *BB)
      if (auto *PN = dyn_cast<PHINode>(&I))
        LiveOuts.insert(&I);
  // TODO: considering the StoreInst
  for (auto *BB : L->getBlocks())
    for (auto &I : *BB) {
      if (isa<StoreInst>(&I))
        LiveOuts.insert(&I);
    }
}

// class Grammar {
// public:
//   class Choice {
//   public:
//     SmallVector<Value *> Terminals;
//     Choice() {};
//     Choice(SmallVector<Value *> Terminals) : Terminals(Terminals) {};
//   };
//   class IndVar : Choice {};
//   class BinOp : Choice {
//   public:
//     Choice *Left;
//     Choice *Right;
//     BinOp(Choice *Left, Choice *Right) : Left(Left), Right(Right){};
//   };
//   class And : BinOp {
//     using BinOp::BinOp;
//   };
//   class Eq : BinOp {
//     using BinOp::BinOp;
//   };
//
//   struct Category {
//     SmallVector<Choice *> Choices;
//   };
//
//   DenseSet<Category *> Categories;
// };
// TODO all based on pointers, so dangerous if MakTerm is run
// after the mapping

// keep track of all terminals used *anywhere* by *any* loop.
// there must be at most 1 Z3 expr and/or 1 CVC5 term associated
// with any terminal.
class TerminalMap {
public:
  TerminalMap(context &c) : c(c), Z3Symbols(c), Z3Functions(c) {}

  expr setZ3(Value *V, expr const& Expr) {
    Z3Symbols.push_back(Expr);
    Z3Map[V] = Z3Symbols.size()-1;
    return getZ3(V);
  }

//  func_decl const& operator[](Value *V) {
//    Z3Functions.resize(Z3Functions.size() + 1);
//    Z3Map[V] = Z3Symbols.size()-1;
//    return Z3Functions[Z3Symbols.size()-1];
//  }

  func_decl setZ3Fun(Value *V, func_decl const& Fun) {
    Z3Functions.push_back(Fun);
    Z3FunMap[V] = Z3Functions.size()-1;
    return Z3Functions.back();
  }

  expr getZ3(Value *V) { return Z3Symbols[Z3Map[V]]; }
  func_decl getZ3Fun(Value *V) { return Z3Functions[Z3FunMap[V]]; }

  bool countZ3(Value *V) { return Z3Map.count(V); }

  context &ctxt() { return c; }

private:
  context &c;
  expr_vector Z3Symbols;
  func_decl_vector Z3Functions;
  std::vector<Term> CVCSymbols;

  DenseMap<Value *, unsigned> Z3Map;
  DenseMap<Value *, unsigned> Z3FunMap;
  DenseMap<Value *, unsigned> CVC5Map;
};

template<typename ExprTy, typename SortTy>
class MakeSMT {
protected:
  using RMapTy = DenseMap<Value *, std::pair<RecurrenceDescriptor, PHINode*>>;
  Loop *L = nullptr;
  LoopInfo *LI = nullptr;
  ScalarEvolution &SE;
  LoopNest *LN = nullptr;
  SmallPtrSet<Value *, 5> BuildRecursive;
  bool LockRecursion = false;
public:
  MakeSMT(TerminalMap &Map, ScalarEvolution &SE) : SE(SE), Map(Map) {}

  ExprTy FromVal(Value *V) {
    // update the current loop
    if (count(V))
      return get(V);
    // either a constant, or an instruction.
    auto Dispatch = [&](Value *V) {
      if (auto *Const = dyn_cast<Constant>(V))
        return FromConst(Const);
      if (isa<Argument>(V))
        return FromPHIorArg(V);

      Instruction *I = dyn_cast<Instruction>(V);
      if (I == nullptr)
        llvm_unreachable("unsupported value type.");

      switch (I->getOpcode()) {
      case Instruction::Load:
      case Instruction::Store:
        return FromLoadStore(I);
      case Instruction::PHI:
        return FromPHIorArg(I);
      case Instruction::FCmp:
      case Instruction::ICmp:
        return FromCmpInst(static_cast<CmpInst*>(I));
      case Instruction::Call:
        return FromCallInst(static_cast<CallInst*>(I));

#define HANDLE_CAST_INST(NUM, OPCODE, CLASS) \
    case Instruction::OPCODE: \
      return FromCastInst(static_cast<CastInst*>(I));
#define HANDLE_BINARY_INST(NUM, OPCODE, CLASS) \
    case Instruction::OPCODE: \
      return FromBinOp(static_cast<BinaryOperator*>(I));
#include "llvm/IR/Instruction.def"

      default:
        llvm_unreachable("unsupported opcode.");
      }
    };

    return set(V, Dispatch(V));
  }

protected:
  TerminalMap &Map;
  struct GEPTy {
    ExprTy Base;
    ExprTy Offset;
  };

  virtual unsigned count(Value *V) = 0;
  virtual ExprTy get(Value *V) = 0;
  virtual ExprTy set(Value *V, const ExprTy &) = 0;

  virtual ExprTy FromConst(Constant *V) = 0;
  virtual ExprTy FromLoadStore(Value *V) = 0;
  virtual GEPTy FromGEP(GEPOperator *V) = 0;
  virtual ExprTy FromCastInst(CastInst *V) = 0;
  virtual ExprTy FromPHIorArg(Value *V) = 0;
  virtual ExprTy FromBinOp(BinaryOperator *V) = 0;
  virtual ExprTy FromCmpInst(CmpInst *V) = 0;
  virtual ExprTy FromCallInst(CallInst *V) = 0;

  virtual SortTy ToSort(Value *V) = 0;
  virtual SortTy ToSort(Type *T) = 0;
};

class MakeZ3 : public MakeSMT<expr, z3::sort> {
public:
  MakeZ3(TerminalMap &Map, ScalarEvolution &SE, context &c) : MakeSMT(Map, SE), c(c) {}

  z3::sort ToSort(Value *V) override {
    auto *T = V->getType();
    switch(T->getTypeID()) {
    default:
      llvm_unreachable("unsupported LLVM type.");
    case Type::TypeID::IntegerTyID:
    case Type::TypeID::DoubleTyID:
      return ToSort(T);
    case Type::TypeID::PointerTyID:
      // try to find a use that we can infer the type from
      for (auto *Use : V->users()) {
        if ((isa<LoadInst>(Use) || isa<StoreInst>(Use)))
          return c.array_sort(c.int_sort(), ToSort(getLoadStoreType(Use)));
        if (auto *GEP = dyn_cast<GEPOperator>(Use))
          return c.array_sort(c.int_sort(), ToSort(GEP->getSourceElementType()));
      }
      llvm_unreachable("couldn't infer the type of the pointer.");
    }
  }

  z3::sort ToSort(Type *T) override {
    unsigned Mantissa, Exponent;
    switch(T->getTypeID()) {
    default:
      llvm_unreachable("unsupported LLVM type.");
    case Type::TypeID::IntegerTyID:
      return c.int_sort();
    case Type::TypeID::DoubleTyID:
      // TODO remove this debug
      //      return c.int_sort();
      Mantissa = APFloat::semanticsPrecision(T->getFltSemantics());
      Exponent = APFloat::semanticsSizeInBits(T->getFltSemantics()) - Mantissa;
      return c.fpa_sort(Exponent, Mantissa);
      //      return c.fpa_sort<64>();
    }
  }

  GEPTy FromGEP(GEPOperator *GEP) override {
    assert(GEP->getNumIndices() == 1);
    // make the array if it doesn't exist
    if (!count(GEP->getPointerOperand())) {
      // TODO assume 1d memory accesses
      z3::sort ArraySort = c.array_sort(
          ToSort(GEP->getOperand(1)),
          ToSort(GEP->getResultElementType()));
      set(
          GEP->getPointerOperand(),
          c.constant(GEP->getPointerOperand()->getName().data(), ArraySort));
    }
    expr Base = get(GEP->getPointerOperand());
    expr Offset = FromVal(GEP->getOperand(1));
    return {Base, Offset};
  }

protected:
  context &c;

  unsigned count(Value *V) override { return Map.countZ3(V); }

  expr get(Value *V) override { return Map.getZ3(V); }

  expr set(Value *V, const expr &Expr) override { return Map.setZ3(V, Expr); }

  expr FromConst(Constant *V) override {
    APSInt Result;
    bool isExact;

    switch (V->getType()->getTypeID()) {
    case Type::TypeID::IntegerTyID:
      return c.int_val(dyn_cast<ConstantInt>(V)->getSExtValue());
    case Type::TypeID::DoubleTyID:
      // TODO remove this debug hack
//      dyn_cast<ConstantFP>(V)->getValue().convertToInteger(Result, APFloatBase::rmNearestTiesToEven, &isExact);
//      return c.int_val(Result.getSExtValue());
      return c.fpa_val(dyn_cast<ConstantFP>(V)->getValue().convertToDouble());
    default:
      llvm_unreachable("unsupported constant type");
    }
  }

  expr FromLoadStore(Value *V) override {
    auto *GEP = dyn_cast<GEPOperator>(getLoadStorePointerOperand(V));
    // eg. y[i]
    GEPTy ArrayAddr = FromGEP(GEP); // (tuple base offset)
    // if store, y[i] = ...  (store)
    // if load %0 = y[i]     (select)
    expr Expr(c);
    if (auto *Store = dyn_cast<StoreInst>(V))
      return store(
          ArrayAddr.Base,
          ArrayAddr.Offset,
          FromVal(Store->getValueOperand()));
    return ArrayAddr.Base[ArrayAddr.Offset];
  }

  expr FromCastInst(CastInst *C) override { return FromVal(C->getOperand(0)); }

  expr FromBinOp(BinaryOperator *BinOp) override {
    auto Left = FromVal(BinOp->getOperand(0));
    auto Right = FromVal(BinOp->getOperand(1));
    switch (BinOp->getOpcode()) {
    case BinaryOperator::BinaryOps::Add:
      return Left + Right;
    case BinaryOperator::BinaryOps::Mul:
      return Left * Right;
    default:
      llvm_unreachable("unsupported binop type.");
    }
  }

  expr FromCmpInst(CmpInst *Cmp) override {
    auto Left = FromVal(Cmp->getOperand(0));
    auto Right = FromVal(Cmp->getOperand(1));
    switch (Cmp->getPredicate()) {
    case CmpInst::ICMP_SLT:
    case CmpInst::ICMP_ULT:
      return Left < Right;
    case CmpInst::ICMP_SGT:
    case CmpInst::ICMP_UGT:
      return Left > Right;
    default:
      llvm_unreachable("unsupported predicate type.");
    }
  }

  expr FromCallInst(CallInst *CI) override {
    auto *F = CI->getCalledFunction();
    if (F && F->getIntrinsicID() == Intrinsic::fmuladd) {
      // a*b + c
      expr A = FromVal(CI->getOperand(0));
      expr B = FromVal(CI->getOperand(1));
      expr C = FromVal(CI->getOperand(2));
      return fma(A, B, C, c.fpa_rounding_mode());
    }
    llvm_unreachable("arbitrary functions aren't supported.");
  }

  expr FromPHIorArg(Value *V) override {
    // check if it's a phi:
//    if (auto *PHI = dyn_cast<PHINode>(V)) {
//      // check whether there are two values and one is NOT from the header
//      BasicBlock *Header = L->getHeader();
//      // TODO should be any indvar, not just the current
//      if (L->getInductionVariable(SE) != PHI) {
//        Value *NextVal = nullptr;
//        for (auto &Use : PHI->incoming_values()) {
//          if (PHI->getIncomingBlock(Use) == PHI->getParent())
//            continue ; // avoid infinite loops
//          if (auto *Inst = dyn_cast<Instruction>(&Use)) {
//            assert(NextVal == nullptr && "only one non-const allowed!");
//            NextVal = Inst;
//          }
//        }
//        if (NextVal) {
//          // assume the loop will execute at least once,
//          // so base the liveout off the non-header value
//          return FromVal(NextVal);
//        }
//      }
//    }
    return c.constant(V->getNameOrAsOperand().c_str(), ToSort(V));
  }
};



class SSA2Func {
  using ConverterTy = MakeZ3;
public:
  SSA2Func(context &Ctx, DominatorTree &DT, ConverterTy &Converter, Value *LiveOut) : Ctx(Ctx), BB2Func(Ctx), DT(DT), Converter(Converter), Range(Ctx), Output(Ctx) {
    if (auto *GEP = dyn_cast<GEPOperator>(getLoadStorePointerOperand(LiveOut))) {
      auto Tuple = Converter.FromGEP(GEP);
      Range = Tuple.Base.get_sort();
      Output = Tuple.Base;
    } else {
      llvm_unreachable("other liveout types aren't supported right now.");
    }
  }

  func_decl fromFunction(Function *F) {
    BasicBlock *BB = &F->getEntryBlock();
    std::vector<Value *> FArgs;
    for (auto &Use : F->args()) FArgs.push_back(&Use);
    Scopes[BB] = makeScope(BB, FArgs);
    makeScopes(BB);
    for (auto &NewBB : *F)
      makeCall(&NewBB);
    return BB2Func.getZ3Fun(BB);
  }

  void makeScopes(BasicBlock *BB) {
    auto &Scope = Scopes[BB];
    // make domain
    std::vector<z3::sort> Domain;
    for (auto *V : Scope) Domain.push_back(Converter.FromVal(V).get_sort());
    BB2Func.setZ3Fun(BB, Ctx.recfun(BB->getNameOrAsOperand().c_str(), Domain.size(), Domain.data(), Range));
    LLVM_DEBUG({
      dbgs() << BB->getNameOrAsOperand() << ": ";
      for (auto S : Domain)
        dbgs() << S.to_string() << " -> ";
      dbgs() << Range.to_string() << "\n";
    });
    auto *Node = DT.getNode(BB);
    for (auto *N : *Node) {
      auto *NewBB = N->getBlock();
      Scopes[NewBB] = makeScope(NewBB, Scope);
      makeScopes(NewBB);
    }
  }

  void makeCall(BasicBlock *BB) {
    expr_vector Scope(Ctx);
    // add to the current scope
    for (auto *V : Scopes[BB])
      Scope.push_back(Converter.FromVal(V));

    if (auto *Ret = dyn_cast<ReturnInst>(BB->getTerminator())) {
      Ctx.recdef(BB2Func.getZ3Fun(BB), Scope, Output);
      return;
    }

    // after setting scopes, start wiring functions together
    auto *Br = dyn_cast<BranchInst>(BB->getTerminator());
    assert(Br != nullptr && "only basic blocks terminating in a branch instruction are supported");
    expr_vector Calls(Ctx);
    for (auto *Block : Br->successors()) {
      expr_vector LocalScope(Ctx);
      for (auto *V : Scopes[Block]) {
        if (auto *Phi = dyn_cast<PHINode>(V)) {
          if (Phi->getBasicBlockIndex(BB) > -1) {
            LocalScope.push_back(
                Converter.FromVal(Phi->getIncomingValueForBlock(BB)));
            continue;
          }
        }
        // otherwise, it MUST be a memory operation.
        // find the corresponding store (in this block):
        bool Found = false;
        for (auto &Inst : *BB) {
          if (auto *Store = dyn_cast<StoreInst>(&Inst)) {
            if (getPointerOperand(getLoadStorePointerOperand(Store)) == V) {
              LocalScope.push_back(Converter.FromVal(Store));
              Found = true;
              break;
            }
          }
        }
        if (!Found)
          LocalScope.push_back(Converter.FromVal(V));
      }
      Calls.push_back(BB2Func.getZ3Fun(Block)(LocalScope));
    }

    expr Body(Ctx);
    if (Br->isUnconditional())
      Body = Calls[0];
    else
      Body = ite(Converter.FromVal(Br->getCondition()), Calls[1], Calls[0]);

    Ctx.recdef(BB2Func.getZ3Fun(BB), Scope, Body);

    LLVM_DEBUG({
      dbgs() << BB->getNameOrAsOperand() << ", [";
      for (unsigned i=0; i < Scope.size()-1; ++i)
        dbgs() << Scope[i].to_string() << ", ";
      dbgs() << Scope.back().to_string() << "]\n";
      dbgs() << Body.to_string() << "\n";
    });
  }

  func_decl operator[](Value *V) {
    return BB2Func.getZ3Fun(V);
  }

private:
  std::vector<Value*> makeScope(BasicBlock *BB, std::vector<Value*> Prefix) {
    for (auto &Inst : *BB) {
      if (auto *Phi = dyn_cast<PHINode>(&Inst))
        Prefix.push_back(Phi);
      else
        break;
    }
    return Prefix;
  }
  context &Ctx;
  DenseMap<Value *, std::vector<Value *>> Scopes;
  TerminalMap BB2Func;
  DominatorTree &DT;
  ConverterTy &Converter;
  z3::sort Range;
  expr Output;
};

PreservedAnalyses RevAnalysisPass::run(Function &F,
                                       FunctionAnalysisManager &AM) {
  errs() << F.getName() << "\n";

  auto start = high_resolution_clock::now();

  AssumptionCache AC = AM.getResult<AssumptionAnalysis>(F);
  DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
  DemandedBits DB(F, AC, DT);
  Module *M = F.getParent();
  LLVMContext &C = M->getContext();

  LoopInfo &LI = AM.getResult<LoopAnalysis>(F);
  ScalarEvolution &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
  for (auto *LP : LI.getTopLevelLoops()) {
    LLVM_DEBUG(dbgs() << " " << *LP << "\n");

    if (!LegalityAnalysis(LP, &LI, &SE)) {
      LLVM_DEBUG(dbgs() << "LLNA: "
                        << "fail to pass legality check \n");
      return PreservedAnalyses::all();
    }

    LoopNest LN(*LP, SE);
    for (int Depth = LN.getNestDepth(); Depth > 0; --Depth) {
      Loop *SubLoop = LN.getLoopsAtDepth(Depth)[0];
      if (!canSupportPhiInstrs(SubLoop, &LI, &DB, &AC, &DT, &SE)) {
        LLVM_DEBUG(dbgs() << "LLNA: "
                          << "fail to pass legality check \n");
        return PreservedAnalyses::all();
      }
    }
  }

  // analysis here
  // live in/out: any scalars used outside the loop, or memory writes in the
  // loop

  LoopNest LN(*LI.getTopLevelLoops()[0], SE);


  context Ctx;
  TerminalMap BB2Func(Ctx), Env(Ctx);
  MakeZ3 Converter(Env, SE, Ctx);
//  Converter.setLoopInfo(&LI);
//  Converter.setLoopNest(&LN);
  Loop *OuterLoop = &LN.getOutermostLoop();

  SmallPtrSet<Value *, 4> LiveOuts;
  GetLiveOuts(OuterLoop, LiveOuts);
  assert(LiveOuts.size() == 1 && "only 1 output tensor supported for now");
  auto *LiveOut = (*LiveOuts.begin());

  expr_vector Arguments(Ctx);
  Value *LiveOutBase = nullptr;
  if (auto *GEP = dyn_cast<GEPOperator>(getLoadStorePointerOperand(LiveOut))) {
    auto Tuple = Converter.FromGEP(GEP);
    Arguments.push_back(Tuple.Base);
    LiveOutBase = GEP->getPointerOperand();
  } else {
    llvm_unreachable("other liveout types aren't supported right now.");
  }

  z3::sort Range = Arguments[0].get_sort();
  SSA2Func Translate(Ctx, DT, Converter, LiveOut);
  Translate.fromFunction(&F);

//  std::vector<z3::sort> Domain = {Arguments[0].get_sort()};
//
//  // TODO make iterative (maybe using df_begin) later
//  z3::sort Range = Arguments[0].get_sort();
//  std::function<void(SmallVector<Value *>, std::vector<z3::sort>, BasicBlock *)> DFS1;
//  DenseMap<Value *, SmallVector<Value *>> Scopes;
//  DFS1 = [&Scopes, &Converter, &Range, &BB2Func, &Ctx, &DT, &DFS1](
//            SmallVector<Value *> Scope,
//            std::vector<z3::sort> Domain,
//            BasicBlock *BB) {
//    for (auto &Inst : *BB) {
//      if (auto *Phi = dyn_cast<PHINode>(&Inst)) {
//        Domain.push_back(Converter.FromVal(Phi).get_sort());
//        Scope.push_back(Phi);
//      } else
//        break;
//    }
//    BB2Func.setZ3Fun(BB, Ctx.recfun(BB->getNameOrAsOperand().c_str(), Domain.size(), Domain.data(), Range));
//    Scopes[BB] = Scope;
//    LLVM_DEBUG({
//       dbgs() << BB->getNameOrAsOperand() << ": ";
//       for (auto S : Domain)
//         dbgs() << S.to_string() << " -> ";
//       dbgs() << Range.to_string() << "\n";
//    });
//    auto *Node = DT.getNode(BB);
//    for (auto *N : *Node) {
//      auto *NewBB = N->getBlock();
//      DFS1(Scope, Domain, NewBB);
//    }
//  };
//
//  DFS1({LiveOutBase}, {Arguments[0].get_sort()}, OuterLoop->getHeader());
//
//  std::function<void(BasicBlock *)> DFS2;
//
//  DFS2 = [&OuterLoop, &Scopes, &Converter, &BB2Func, &Ctx, &DT, &DFS2](
//             BasicBlock *BB) {
//    auto *Br = dyn_cast<BranchInst>(BB->getTerminator());
//    assert(Br != nullptr && "only basic blocks terminating in a branch instruction are supported");
//
//
//
//    expr_vector Calls(Ctx);
//
//    for (auto *Block : Br->successors()) {
//      expr_vector Scope(Ctx);
//      for (auto *V : Scopes[Block]) {
//        if (auto *Phi = dyn_cast<PHINode>(V)) {
//          if (Phi->getBasicBlockIndex(BB) > -1) {
//            Scope.push_back(
//                Converter.FromVal(Phi->getIncomingValueForBlock(BB)));
//            continue;
//          }
//        }
//        // otherwise, it MUST be a memory operation.
//        // find the corresponding store (in this block):
//        bool Found = false;
//        for (auto &Inst : *BB) {
//          if (auto *Store = dyn_cast<StoreInst>(&Inst)) {
//            if (getPointerOperand(getLoadStorePointerOperand(Store)) == V) {
//              Scope.push_back(Converter.FromVal(Store));
//              Found = true;
//              break;
//            }
//          }
//        }
//        if (!Found)
//          Scope.push_back(Converter.FromVal(V));
//      }
//      Calls.push_back(BB2Func.getZ3Fun(Block)(Scope));
//    }
//
//    // add to the current scope
//    expr_vector Scope(Ctx);
//    for (auto *V : Scopes[BB])
//      Scope.push_back(Converter.FromVal(V));
//
//    expr Body(Ctx);
//    if (OuterLoop->getUniqueExitBlock() == BB)
//      Body = Scope[0];
//    else if (Br->isUnconditional())
//      Body = Calls[0];
//    else
//      Body = ite(Converter.FromVal(Br->getCondition()), Calls[1], Calls[0]);
//
//    Ctx.recdef(BB2Func.getZ3Fun(BB), Scope, Body);
//
//    LLVM_DEBUG({
//      dbgs() << BB->getNameOrAsOperand() << ", [";
//      for (unsigned i=0; i < Scope.size()-1; ++i)
//        dbgs() << Scope[i].to_string() << ", ";
//      dbgs() << Scope.back().to_string() << "]\n";
//      dbgs() << Body.to_string() << "\n";
//    });
//
//    auto *Node = DT.getNode(BB);
//    for (auto *N : *Node) {
//      auto *NewBB = N->getBlock();
//      DFS2(NewBB);
//    }
//  };
//
//
//  DFS2(OuterLoop->getHeader());

//  func_decl_vector Kernels(Ctx);
//  struct KernelRecord {
//    unsigned Idx;
//    std::string Path;
//  };
//  std::vector<KernelRecord> KRecords = {
//      {0, "gemv_opt.ll"}
//  };
//
//  func_decl_vector StorageFormats(Ctx);
//
//  for (auto &R : KRecords) {
//
//  }



  solver Slv(Ctx);
  Value *N = F.getArg(0);
  Value *Rptr = F.getArg(1);
  Value *Col = F.getArg(2);
  Value *Val = F.getArg(3);
  Value *X = F.getArg(4);
  Value *Y = F.getArg(5);

//  expr n = Converter.FromVal(N);
//  expr rptr = Converter.FromVal(Rptr);
//  expr val = Converter.FromVal(Val);
//  LLVM_DEBUG(dbgs() << val.to_string() << ": " << val.get_sort().to_string() << "\n");
//  expr col = Converter.FromVal(Col);
//  expr x = Converter.FromVal(X);
//  expr y = Converter.FromVal(Y);
  expr zero = Ctx.int_val(0);
  expr one = Ctx.int_val(1);
  expr two = Ctx.int_val(2);

//  Slv.add(n == 2);
//  Slv.add(val[zero] == 1);
//  Slv.add(val[one] == 1);
//
//  Slv.add(rptr[zero] == 0);
//  Slv.add(rptr[one] == 1);
//  Slv.add(rptr[two] == 2);
//
//  Slv.add(col[zero] == 1);
//  Slv.add(col[one] == 0);
//
//  Slv.add(y[zero] == 0);
//  Slv.add(y[one] == 0);
//
//  Slv.add(x[zero] == 1);
//  Slv.add(x[one] == 2);
  expr n = Ctx.int_val(2);
  Slv.add(n == 2);
  expr rptr = Converter.FromVal(Rptr);
  expr val = Converter.FromVal(Val);
  expr col = Converter.FromVal(Col);
  expr x = Converter.FromVal(X);
  expr y = Converter.FromVal(Y);
//  val = store(val, 0, 1);
//  val = store(val, 1, 1);
//  rptr = store(rptr, 0, 0);
//  rptr = store(rptr, 1, 1);
//  rptr = store(rptr, 2, 2);
//  col = store(col, 0, 1);
//  col = store(col, 1, 0);
//  y = store(y, 0, 0);
//  y = store(y, 1, 0);
//  x = store(x, 0, 1);
//  x = store(x, 1, 2);
    Slv.add(val[zero] == 1);
    Slv.add(val[one] == 1);

    Slv.add(rptr[zero] == 0);
    Slv.add(rptr[one] == 1);
    Slv.add(rptr[two] == 2);

    Slv.add(col[zero] == 1);
    Slv.add(col[one] == 0);

    Slv.add(y[zero] == 0);
    Slv.add(y[one] == 0);

    Slv.add(x[zero] == 1);
    Slv.add(x[one] == 2);


  auto Result = Slv.check();
  if (Result == z3::sat) {
    auto Model = Slv.get_model();
    std::vector<expr> Args = {n, rptr, col, val, x, y};
    auto Output = Translate[&F.getEntryBlock()](Args.size(), Args.data());
    LLVM_DEBUG({
      dbgs() << "Concrete Test output: \n";
      for (int i=0; i < n.as_int64(); ++i) {
        auto elem = Model.eval(Output[Ctx.int_val(i)].simplify());
        dbgs() << Z3_get_numeral_string(Ctx, elem) << " ";
      }
      dbgs() << "\n";
    });
  }


  return PreservedAnalyses::all();

//  for (int Depth = LN.getNestDepth(); Depth > 0; --Depth) {
//    Loop *L = LN.getLoopsAtDepth(Depth)[0];
//    Converter.setLoop(L);
//
//    // (2) Figure out the liveout
//    SmallPtrSet<Value *, 4> LiveOuts;
//    GetLiveOuts(L, LiveOuts);
//    assert(LiveOuts.size() == 1 && "only 1 output tensor supported for now");
//    auto *LiveOut = (*LiveOuts.begin());
//
//    // (3) Try to make the VCs from the live out
//
//
////    PostConditionBuilder<expr, z3::sort> Z3PC(Converter);
//
//
//
//
//    PHINode *IndVar = L->getInductionVariable(SE);
//    LLVM_DEBUG(dbgs() << "Rev: Induction Variable is " << *IndVar << "\n");
//    //    Solver slv;
//    Loop2Converter[L] = new CVCConv;
//    CVCConv *CConv = Loop2Converter[L];
//
//
//
//    // Then also get the live out
//    Value *LLVMLiveOut = (*LiveOuts.begin());
//    LLVM_DEBUG(dbgs() << "Rev: live out is " << *LLVMLiveOut << "\n");
//    Value *LiveOutEnd = nullptr;
//    if (isa<PHINode>(LLVMLiveOut)) {
//      LLVMLiveOut = dyn_cast<PHINode>(LLVMLiveOut)->getOperand(0);
//      if (RecDecs.count(LLVMLiveOut)) {
//        // TODO: here there is one assumption about reduction, all the
//        // computation are performed using one single instruction
//        RecurrenceDescriptor &RD = RecDecs[LLVMLiveOut].first;
//        LLVMLiveOut = RecDecs[LLVMLiveOut].second;
//        LiveOutEnd =
//            RD.getReductionOpChain(dyn_cast<PHINode>(LLVMLiveOut), L)[0];
//
//        LLVM_DEBUG(dbgs() << "Rev: LiveOutEnd is " << *LiveOutEnd << "\n");
//      }
//      CConv->liveout = CConv->MakeTerm(LLVMLiveOut, Ins2Terms);
//    } else { // must be store
//      auto *Store = dyn_cast<StoreInst>(LLVMLiveOut);
//      auto *GEP =
//          dyn_cast<GEPOperator>(Store->getPointerOperand()); // get the GEP
//      LLVMLiveOut = GEP->getPointerOperand(); // then get the base ptr
//      LiveOutEnd = Store;
//      // make the GEP:
//      CConv->MakeTerm(GEP, Ins2Terms);
//      // we only want the base
//      CConv->liveout = &Ins2Terms[LLVMLiveOut];
//    }
//    CConv->liveoutend = LiveOutEnd;
//
//    LLVM_DEBUG(dbgs() << "Rev: live out is " << CConv->liveout->toString()
//                      << "\n");
//    LLVM_DEBUG(dbgs() << "Rev: live out end is " << *(CConv->liveoutend)
//                      << "\n");
//
//    // Now, have to define the sum function for any phis
//    // let's use a generic version and store it in CConv
//
//    // Then have to create the postcondition/invariant grammar:
//    // INV GRAMMAR:
//    // start := (and <cmp> <cmp> <eq>))
//    // cmp   := <expr> <= <expr>
//    // expr  := lb | invariant | ub
//    // eq    := {forall if eq is memory store} <single out> = <valid ops>
//    // valid_ops :=
//    //           | try to create sum from phi
//    //           | + | - | * | ...
//
//    // PC GRAMMAR:
//    // start :=  (and <eq1>  ({forall if eq is memory store} <eq2>))
//    // eq1      := lb == ub
//    // eq2      := eq {where all phis have exit val}
//
//    // find the loop bounds
//    auto Bounds = L->getBounds(SE);
//    auto *UB = &Bounds->getFinalIVValue();
//    auto *LB = &Bounds->getInitialIVValue();
//    auto *INDVAR = L->getInductionVariable(SE);
//    CConv->ub = CConv->MakeTerm(UB, Ins2Terms);
//    CConv->lb = CConv->MakeTerm(LB, Ins2Terms);
//    CConv->indvar = CConv->MakeTerm(INDVAR, Ins2Terms);
//
//    // translate the computation for the liveout
//    CVCConv::UFInfo liveout_compute_chain =
//        CConv->MakeComputeChain(FunctionBodies, LiveOutEnd, L, Ins2Terms, RecDecs);
//    LLVM_DEBUG(dbgs() << "COMPUTE CHAIN:\n");
//    LLVM_DEBUG(dbgs() << liveout_compute_chain.UF.toString() << "\n");
//
//    CConv->MakeTerminals(L, &SE, liveout_compute_chain, Ins2Terms);
//
//    auto inv_gram = CConv->MakeInvGram(liveout_compute_chain);
//
//    // next, make the PC grammar
//    Grammar pc_gram = CConv->MakePCGrammar(liveout_compute_chain);
//
//    std::vector<CVCConv::GrammarRecord> GR = {{inv_gram, "inv"},
//                                              {pc_gram, "pc"}};
//    CConv->MakeSynthFuns(GR);
//    CConv->MakeUniversalVars(GR);
//    CConv->MakeSynthFunCalls();
//    CConv->MakeVerificationConditions(&LN, L, Ins2Terms,Loop2Converter);
//
//    // at this point, also need to figure out the mapping
//
//  }
//
//  // make a forest of possible replacements
//  Term FinalPC;
//  for (int Depth = LN.getNestDepth()-1; Depth > 0; --Depth) {
//    Loop *Linner = LN.getLoopsAtDepth(Depth+1)[0];
//    auto *Cinner = Loop2Converter[Linner];
//    Loop *Louter = LN.getLoopsAtDepth(Depth)[0];
//    auto *Couter = Loop2Converter[Louter];
//    for (auto &P : Couter->PCRegister)
//      if (P.first == *Couter->liveout) {
//        FinalPC = P.second;
//        auto *Inst = dyn_cast<Instruction>(Couter->liveoutend);
//        SmallVector<BasicBlock*> ExitBlock;
//        Linner->getExitBlocks(ExitBlock);
//        for (auto &I : *ExitBlock[0]) {
//          auto *PN = dyn_cast<PHINode>(&I);
//          if (PN == nullptr || PN->getIncomingValue(0) != Cinner->liveoutend)
//            break;
//          for (auto *User : PN->users()) {
//            FinalPC = FinalPC.substitute(*Couter->MakeTerm(User, Ins2Terms), Cinner->PCRegister[0].second);
//          }
//        }
//        break;
//      }
//  }
//
//  LLVM_DEBUG(dbgs() << "Final PC: " << FinalPC.toString() << "\n");
//  // for now, just convert to z3
//  // build a symbol table
//  DenseMap<StringRef, Term> SymbolTable;
//  for (auto &P : FunctionBodies)
//    SymbolTable[std::get<0>(P).toString()] = std::get<2>(P);
//  // first convert all the functions
//  Z3Mapping Mapping(c);
//  // TODO this will need to be split into two loops,
//  // first make all symbols, then make maps, then make all functions
//  for (auto &P : FunctionBodies) {
//    std::vector<z3::sort> Domain;
//    expr_vector &Args = Mapping.symbols();
//    for (auto &E : std::get<1>(P))
//      Domain.push_back(CVCSort2Z3Sort(E.getSort(), c));
//    for (auto &E : std::get<1>(P)) {
//      Args.push_back(CVC2Z3(Mapping, c, E));
//    }
//    z3::sort Range = CVCSort2Z3Sort(std::get<2>(P).getSort(), c);
//    // make the signature
//    Mapping.functions().push_back(c.recfun(
//        std::get<0>(P).toString().c_str(),
//        Domain.size(),
//        Domain.data(),
//        Range));
//    LLVM_DEBUG(dbgs() << Mapping.functions().back().to_string() << "\n");
//    Mapping.MakeMaps();
//    auto Body = CVC2Z3(Mapping, c, std::get<2>(P));
//    c.recdef(Mapping.functions().back(), Args, Body);
//    LLVM_DEBUG(dbgs() << Body.to_string() << "\n");
//  }
//
//  expr Z3PC = CVC2Z3(Mapping, c, FinalPC);
//  LLVM_DEBUG(dbgs() << Z3PC.to_string() << "\n");
//
//  LLVM_DEBUG(dbgs() << "----------\nMAPPING START\n----------\n");
//
//  auto *ConvOuter = Loop2Converter[&LN.getOutermostLoop()];
//  auto *FinalLiveOut = dyn_cast<Instruction>(ConvOuter->liveoutend);
//
//  // try to inspect arrays
//  FindInputTensors FT(SE, &LI);
//  FT.visitTopLevel(FinalLiveOut);
//  FT.ConstructDenseTensors(Mapping, c, Ins2Terms, ConvOuter->liveout, Z3PC);
//
//  for (auto C : Loop2Converter)
//    delete C.second;
//
//
//
//  return PreservedAnalyses::all();
}