#include "llvm/Analysis/RevAnalysis.h"
#include "z3++.h"
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
      return c.constant(InputTerm.getSymbol().c_str(),
                        CVCSort2Z3Sort(InputTerm.getSort(), c));
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
class CVCConv {
public:
  Solver slv;
  DenseMap<int, Sort> SpecialSorts;
  SmallSet<Term *, 16> Leaves;
  Term RoundingMode;
  std::vector<Term *> SumArgs;
  std::vector<Term *> Terminals;
  DenseMap<Term *, Value *> Terms2Vals;
  DenseMap<Term *, Value *> Uni2Vals;
  Term *lb;
  Term *ub;
  Term *indvar;

  Term *liveout; // reduction phi in header section
  Value *liveoutend;  // the end of reduction phi

  DenseMap<StringRef, Term> SynthFuns;
  DenseMap<Term *, Term> UniversalVars;
  DenseMap<StringRef, Term> SynthFunCalls;
  Sort fpsort;
  Term pc;
  // TODO destroy this in CVCConv destructor
  // this is really inefficient but DenseMap was mangling the stringrefs all the time,
  // couldn't figure out why
  std::vector<std::pair<Term, Term>> PCRegister; // stores equality relationships from PC

  class UFInfo {
  public:
    std::vector<Term> BoundTerms;
    Term UF;
    std::vector<Value *> ArgVals;
    UFInfo(std::vector<Term> BT, Term UF, std::vector<Value *> AV) : BoundTerms(BT), UF(UF), ArgVals(AV) {}
  };

  CVCConv() {
    slv.setOption("sygus", "true");
    slv.setOption("incremental", "false");
    slv.setOption("sygus-rec-fun", "true");
    slv.setOption("fmf-fun", "true");
    slv.setOption("output", "sygus");
    fpsort = slv.mkFloatingPointSort(11, 53);
    // TODO assumes double, add float
    SpecialSorts[Type::TypeID::DoubleTyID] = fpsort;
    // TODO assume the same rounding mode for all operations
    RoundingMode = slv.mkRoundingMode(ROUND_NEAREST_TIES_TO_EVEN);
  };

  Sort ToSort(Type *T) {
    if (T->getTypeID() == Type::TypeID::IntegerTyID)
      return slv.getIntegerSort();
    if (T->getTypeID() == Type::TypeID::DoubleTyID)
      return SpecialSorts[T->getTypeID()];
    assert(0 && "unsupported LLVM Type");
  }

  Term *MakeTerm(Value *V, DenseMap<Value *, Term> &Env) {
    if (Env.count(V))
      return &Env[V];
    if (auto *Const = dyn_cast<Constant>(V)) {
      switch (Const->getType()->getTypeID()) {
      case Type::TypeID::IntegerTyID:
        return &(Env[V] =
                     slv.mkInteger(dyn_cast<ConstantInt>(V)->getSExtValue()));
        break;
      case Type::TypeID::DoubleTyID:
        return &(
            Env[V] = slv.mkFloatingPoint(
                11, 53,
                slv.mkBitVector(
                    64,
                    dyn_cast<ConstantFP>(V)->getValue().convertToDouble())));
      default:
        assert(0 && "unsupported constant type");
        break;
      }
    } else if (isa<LoadInst>(V) || isa<StoreInst>(V)) {
      auto *GEP = dyn_cast<GEPOperator>(getLoadStorePointerOperand(V));
      // eg. y[i]
      Term *ArrayAddr = MakeTerm(GEP, Env); // (tuple base offset)
      // if store, y[i] = ...  (store)
      // if load %0 = y[i]     (select)
      Kind ArrayOp = isa<LoadInst>(V) ? SELECT : STORE;
      std::vector<Term> ArgArray = {ArrayAddr->operator[](1),
                                    ArrayAddr->operator[](2)};
      if (auto *Store = dyn_cast<StoreInst>(V))
        ArgArray.push_back(*MakeTerm(Store->getValueOperand(), Env));
      return &(Env[V] = slv.mkTerm(ArrayOp, ArgArray));
    } else if (auto *GEP = dyn_cast<GEPOperator>(V)) {
      assert(GEP->getNumIndices() == 1);
      // make the array if it doesn't exist
      if (!Env.count(GEP->getPointerOperand())) {
        // TODO assume 1d memory accesses
        Sort asort = slv.mkArraySort(ToSort(GEP->getOperand(1)->getType()),
                                     ToSort(GEP->getResultElementType()));
        Env[GEP->getPointerOperand()] =
            slv.mkVar(asort, GEP->getPointerOperand()->getNameOrAsOperand());
        Leaves.insert(&Env[GEP->getPointerOperand()]);
      }
      //      return &(Env[V] =
      //                 slv.mkTerm(SELECT, {*&Env[GEP->getPointerOperand()],
      //                 *MakeTerm(GEP->getOperand(1), Env)}));
      Term *Base = &Env[GEP->getPointerOperand()];
      Term *Offset = MakeTerm(GEP->getOperand(1), Env);
      return &(Env[V] = slv.mkTuple({Base->getSort(), Offset->getSort()},
                                    {*Base, *Offset}));
    } else if (auto *Cast = dyn_cast<CastInst>(V)) {
      return &(Env[V] = *MakeTerm(Cast->getOperand(0), Env));
    } else if (isa<PHINode>(V) || isa<Argument>(V)) {
      Env[V] = slv.mkVar(ToSort(V->getType()), V->getNameOrAsOperand());
      Leaves.insert(&Env[V]);
      return &Env[V];
    } else if (auto *BinOp = dyn_cast<BinaryOperator>(V)) {
      switch (BinOp->getOpcode()) {
      case BinaryOperator::BinaryOps::Add:
        return &(Env[V] =
                     slv.mkTerm(ADD, {*MakeTerm(BinOp->getOperand(0), Env),
                                      *MakeTerm(BinOp->getOperand(1), Env)}));
      case BinaryOperator::BinaryOps::Mul:
        return &(Env[V] =
                     slv.mkTerm(MULT, {*MakeTerm(BinOp->getOperand(0), Env),
                                      *MakeTerm(BinOp->getOperand(1), Env)}));
      default:
        assert(0 && "unsupported binop type.");
        break;
      }
    } else if (auto *Cmp = dyn_cast<CmpInst>(V)) {
      switch (Cmp->getPredicate()) {
      case CmpInst::ICMP_SLT:
        return &(Env[V] = slv.mkTerm(LT, {*MakeTerm(Cmp->getOperand(0), Env),
                                          *MakeTerm(Cmp->getOperand(1), Env)}));
      default:
        assert(0 && "unsupported predicate type.");
        break;
      }
    } else if (auto *CI = dyn_cast<CallInst>(V)) {
      auto *F = CI->getCalledFunction();
      if (F && F->getIntrinsicID() == Intrinsic::fmuladd) {
        // a*b + c
        Term *a = MakeTerm(CI->getOperand(0), Env);
        Term *b = MakeTerm(CI->getOperand(1), Env);
        Term *c = MakeTerm(CI->getOperand(2), Env);
        Env[V] = slv.mkTerm(
            FLOATINGPOINT_ADD,
            {RoundingMode,
             slv.mkTerm(FLOATINGPOINT_MULT, {RoundingMode, *a, *b}), *c});
        return &Env[V];
      } else {
        assert(0 && "arbitrary functions aren't supported.");
      }
    }

    assert(0 && "unsupported value");
    return &(Env[V] = slv.mkBoolean(false));
  }

  // TODO make a general visitor pattern to unify MakeTerm and RetrieveLeaves
  void RetrieveLeaves(Value *V, DenseMap<Value *, Term> &Env,
                      SmallPtrSet<Term *, 8> &LocalLeaves) {
    if (auto *Const = dyn_cast<Constant>(V)) {
      return;
    } else if (isa<LoadInst>(V) || isa<StoreInst>(V)) {
      RetrieveLeaves(getLoadStorePointerOperand(V), Env, LocalLeaves);
      if (auto *Store = dyn_cast<StoreInst>(V))
        RetrieveLeaves(Store->getValueOperand(), Env, LocalLeaves);
      return;
    } else if (auto *GEP = dyn_cast<GEPOperator>(V)) {
      LocalLeaves.insert(&Env[GEP->getPointerOperand()]);
      RetrieveLeaves(GEP->getOperand(1), Env, LocalLeaves);
      return;
    } else if (auto *Cast = dyn_cast<CastInst>(V)) {
      return RetrieveLeaves(Cast->getOperand(0), Env, LocalLeaves);
    } else if (isa<PHINode>(V) || isa<Argument>(V)) {
      LocalLeaves.insert(&Env[V]);
      return;
    } else if (auto *BinOp = dyn_cast<BinaryOperator>(V)) {
      switch (BinOp->getOpcode()) {
      case BinaryOperator::BinaryOps::Add:
        RetrieveLeaves(BinOp->getOperand(0), Env, LocalLeaves);
        RetrieveLeaves(BinOp->getOperand(1), Env, LocalLeaves);
        break;
      case BinaryOperator::BinaryOps::Mul:
        RetrieveLeaves(BinOp->getOperand(0), Env, LocalLeaves);
        RetrieveLeaves(BinOp->getOperand(1), Env, LocalLeaves);
        break;
      default:
        assert(0 && "unsupported binop type.");
        break;
      }
      return;
    } else if (auto *Cmp = dyn_cast<CmpInst>(V)) {
      switch (Cmp->getPredicate()) {
      case CmpInst::ICMP_SLT:
        RetrieveLeaves(Cmp->getOperand(0), Env, LocalLeaves);
        RetrieveLeaves(Cmp->getOperand(1), Env, LocalLeaves);
        break;
      default:
        assert(0 && "unsupported predicate type.");
        break;
      }
      return;
    }else if(auto *CI = dyn_cast<CallInst>(V)){
      auto *F = CI->getCalledFunction();
      if(F && F->getIntrinsicID() == Intrinsic::fmuladd){
        RetrieveLeaves(CI->getOperand(0), Env, LocalLeaves);
        RetrieveLeaves(CI->getOperand(1), Env, LocalLeaves);
        RetrieveLeaves(CI->getOperand(2), Env, LocalLeaves);
      }
      return;
    }


    assert(0 && ("unsupported value " + V->getNameOrAsOperand()).data());
    return;
  }

  UFInfo MakeComputeChain(
      std::vector<std::tuple<Term, std::vector<Term>, Term>> &FunctionBodies,
      Value *V, Loop *L, DenseMap<Value *, Term> &Env,
      DenseMap<Value *, std::pair<RecurrenceDescriptor, PHINode *>> &RecDecs) {
    // Everything is uninterpreted functions.
    // This module tries to represent the liveout operation chain
    // as a single UF over all Phi nodes. For example, consider a liveout store:
    // store double %sum, ptr %arrayidx   (where arrayidx represents y[i])
    // in a loop with a single Phi node in the header, the indvar %i.
    // This should be wrapped in an UF loop(lb_i, ub_i, y[i] = sum)
    // lb_i and ub_i will be supplied later by the inv and pc grammars,
    // but practically it will be the Bounds.getInitialIV and
    // L->getInductionVariable() - 1

    if (RecDecs.count(V)) {
      // liveout is described by a phi!
      RecurrenceDescriptor RD = RecDecs[V].first;
      PHINode *PN = RecDecs[V].second;
      auto Chain = RD.getReductionOpChain(PN, L);
      // detect case when llvm converts to fma
      if (Chain.size() == 1) {
        if (auto *CI = dyn_cast<CallInst>(Chain[0])) {
          auto *F = CI->getCalledFunction();
          if (F && F->getIntrinsicID() == Intrinsic::fmuladd) {
            //            auto Bounds = L->getBounds(*SE);
            // from is the lower bound, that for now is any term
            //            Term from = MakeTerm(&Bounds->getInitialIVValue(),
            //            Env);
            Term from = slv.mkVar(slv.getIntegerSort(), "from");
            // copy the leaves then use them to get the atoms here
            //            auto LeavesBackup = Leaves;
            //            Leaves.clear();
            //            DenseMap<Value *, Term> LocalEnv;

            // to is the upper bound, that we assume is the indvar
            // also we assume the a and b vars all change w.r.t a single Phi
            // TODO assert that this is true
            Term to = slv.mkVar(slv.getIntegerSort(), "to");
            //            Term c = MakeTerm(CI->getOperand(2), LocalEnv);
            Term *a = MakeTerm(CI->getOperand(0), Env);
            Term *b = MakeTerm(CI->getOperand(1), Env);
            std::vector<Value *> ArgVals = {CI->getOperand(0),
                                            CI->getOperand(1)};

            SmallPtrSet<Term *, 8> BoundVars;
            RetrieveLeaves(CI->getOperand(0), Env, BoundVars);
            RetrieveLeaves(CI->getOperand(1), Env, BoundVars);
            // copy into non-ptr array
            //            std::vector<Term> BoundVars2;
            for (auto *T : BoundVars)
              if (T == indvar)
                continue; // skip indvar
              else
                SumArgs.push_back(T);
            for (auto *T : SumArgs)
              LLVM_DEBUG(dbgs() << T->toString() << "\n");

            std::vector<Sort> Sorts;
            std::vector<Term> SumArgsLocal;
            Sorts.push_back(from.getSort());
            Sorts.push_back(to.getSort());
            for (auto *Arg : SumArgs) {
              Sorts.push_back(Arg->getSort());
              SumArgsLocal.push_back(*Arg);
            }
            Sort SumSort = slv.mkFunctionSort(Sorts, ToSort(CI->getType()));
            Term SumDec = slv.mkConst(
                SumSort, ("recurrence_" + CI->getNameOrAsOperand()).data());
            std::vector<Term> InductionStepChildren = {
                SumDec, from, slv.mkTerm(SUB, {to, slv.mkInteger(1)})};
            InductionStepChildren.insert(InductionStepChildren.end(),
                                         SumArgsLocal.begin(),
                                         SumArgsLocal.end());
            Term InductionStep = slv.mkTerm(APPLY_UF, InductionStepChildren);
            Term Mult = slv.mkTerm(FLOATINGPOINT_MULT, {RoundingMode, *a, *b});
            // add = mult + induction step
            // a*b + c
            Term FMA = slv.mkTerm(cvc5::FLOATINGPOINT_ADD,
                                  {RoundingMode, InductionStep, Mult});
            Term SumBody = slv.mkTerm(
                ITE, {slv.mkTerm(LT, {to, from}),
                      *MakeTerm(ConstantFP::get(CI->getType(), 0), Env), FMA});
            std::vector<Term> TotalVars;
            TotalVars.push_back(from);
            TotalVars.push_back(to);
            TotalVars.insert(TotalVars.end(), SumArgsLocal.begin(),
                             SumArgsLocal.end());
            Term SumFunc = slv.defineFunRec(SumDec, TotalVars, SumBody);
            FunctionBodies.push_back({SumFunc, TotalVars, SumBody});
            //            Leaves = LeavesBackup;

            //            // finally, specialize to the loop bounds
            //            Term *lower = MakeTerm(&Bounds->getInitialIVValue(),
            //            Env); Term upper = slv.mkTerm(SUB,
            //            {*MakeTerm(L->getInductionVariable(*SE), Env),
            //            slv.mkInteger(1)}); std::vector<Term> FnArgs;
            //            FnArgs.push_back(SumDec);
            //            FnArgs.push_back(*lower);
            //            FnArgs.push_back(upper);
            //            FnArgs.insert(FnArgs.end(), SumArgsLocal.begin(),
            //            SumArgsLocal.end()); assert(FnArgs.size() ==
            //            SumArgsLocal.size() + 3 && "some bound vars are
            //            missing");
            //
            //            std::vector<Term> AllBoundVars;
            //            AllBoundVars.push_back(*MakeTerm(L->getInductionVariable(*SE),
            //            Env)); AllBoundVars.insert(AllBoundVars.end(),
            //            SumArgsLocal.begin(), SumArgsLocal.end());
            //
            //            Term call = slv.mkTerm(APPLY_UF, FnArgs);
            return {{}, SumDec, ArgVals};
          } else {
            assert(0 && "arbitrary function calls are not supported");
          }
        } else {
          assert(0 && "reduction is not in intrinsic function");
        }
      } else {
        assert(0 && "reduction with chain>1");
      }
    } else if (auto *Store = dyn_cast<StoreInst>(V)) {
      // calculate compute chain for a store.
      // the value might depend on inner loops.
      // if so, it is the PC for that loop.
      Term *Chain = MakeTerm(Store, Env); // (STORE base offset val)
      Term Probe = slv.mkTerm(SELECT, {Chain->operator[](0), Chain->operator[](1)});
      LLVM_DEBUG(dbgs() << "Rev: Chain is " << Chain->toString() << "\n");

      LLVM_DEBUG(dbgs() << "Rev: Probe is " << Probe.toString() << "\n");
      SmallPtrSet<Term *, 8> LLeaves;
      RetrieveLeaves(Store, Env, LLeaves);
      SumArgs.insert(SumArgs.begin(), LLeaves.begin(), LLeaves.end());
      std::vector<Term> BoundVars;
      for (auto * T : LLeaves) BoundVars.push_back(*T);
      auto ArraySort = Chain->operator[](0).getSort();
      auto StoreValSort = Chain->operator[](2).getSort();
      // these are dummy vars just to fit the template
      Term from = slv.mkVar(slv.getIntegerSort(), "from");
      Term to = slv.mkVar(slv.getIntegerSort(), "to");
      BoundVars.insert(BoundVars.begin(), to);
      BoundVars.insert(BoundVars.begin(), from);
      auto FunDef = slv.defineFun("StoreFun", BoundVars, ArraySort, *Chain);
//      Kind EqKind = ToSort(Store->getValueOperand()->getType()) == slv.getIntegerSort() ? EQUAL : FLOATINGPOINT_EQ;
//      Term Eq = slv.mkTerm(EqKind, {Probe, *MakeTerm(Store->getValueOperand(), Env)});
      std::vector<Value *> FnVals;
      for (int i = 0; i < Store->getNumOperands(); ++i)
        FnVals.push_back(Store->getOperand(i));

      FunctionBodies.push_back({FunDef, BoundVars, *Chain});
//
//      Term *ToEq = MakeTerm(Store->getValueOperand(), Env);
//      // collect all the phis, these are args to the loop UF
//      std::vector<Term> FnArgs;
//      std::vector<Value *> FnVals;
//      std::vector<Term> Bounds;
//      std::vector<Term> Phis;
//      std::vector<Sort> Sorts;
//      for (auto &I : *L->getHeader()) {
//        if (auto *PN = dyn_cast<PHINode>(&I)) {
//          Term *Phi = MakeTerm(PN, Env);
//          Phis.push_back(*Phi);
//          FnArgs.push_back(slv.mkVar(ToSort(PN->getType()),
//                                     "lb_" + PN->getNameOrAsOperand()));
//          FnArgs.push_back(slv.mkVar(ToSort(PN->getType()),
//                                     "ub_" + PN->getNameOrAsOperand()));
//          Bounds.push_back(slv.mkTerm(
//              AND, {slv.mkTerm(LEQ, {FnArgs[FnArgs.size() - 2], *Phi}),
//                    slv.mkTerm(LT, {*Phi, FnArgs[FnArgs.size() - 1]})}));
//          Sorts.push_back(ToSort(PN->getType()));
//          Sorts.push_back(ToSort(PN->getType()));
//          FnVals.push_back(PN);
//        } else
//          break;
//      }
//      std::vector<Term> BodyList = Phis;
//      BodyList.insert(BodyList.end(), slv.mkTerm(IMPLIES, {(Bounds.size() == 1 ? Bounds[0] : slv.mkTerm(AND, Bounds)), slv.mkTerm(EqKind, {*ToEq,*Chain})}));
//      Term Body = slv.mkTerm(FORALL, BodyList);
//      Sort FnSort = slv.mkFunctionSort(Sorts, Chain->getSort());
//      Term FnDef = slv.defineFun(L->getName().str(), FnArgs, FnSort, *Chain);
      return {{}, FunDef, FnVals};
    } else {
      assert(0 && "liveout must be described as a phi right now.");
    }
  }

  struct GrammarRecord {
    Grammar &G;
    StringRef Name;
  };

  void MakeSynthFuns(std::vector<GrammarRecord> &Grammars) {
    std::vector<Term> BoundVars;
    for (auto *T : Terminals)
      BoundVars.push_back(*T);

    for (auto GR : Grammars)
      SynthFuns[GR.Name] =
          slv.synthFun(GR.Name.str(), BoundVars, slv.getBooleanSort(), GR.G);
  }

  void MakeUniversalVars(std::vector<GrammarRecord> &Grammars) {
    for (auto *T : Terminals)
      UniversalVars[T] =
          slv.declareSygusVar("sys_" + T->getSymbol(), T->getSort());
  }

  void MakeSynthFunCalls() {
    for (auto Elem : SynthFuns) {
      std::vector<Term> Args = {Elem.second};
      for (auto *T : Terminals)
        Args.push_back(UniversalVars[T]);
      SynthFunCalls[Elem.first] = slv.mkTerm(APPLY_UF, Args);
    }
  }

  void MakeVerificationConditions(LoopNest *LN, Loop *L, DenseMap<Value *, Term> &Env, DenseMap<Loop *, CVCConv*> &Loop2Converter) {
    // modify env to inject the universalvars where the previous values were
    // TODO clean up this whole pointers mess, we need a better way to test
    // equality
    //    for (auto &Elem : UniversalVars) {
    //      Env[Terms2Vals[Elem.first]] = Elem.second;
    //    }
    Term Precondition = slv.mkBoolean(false); // TODO fix this hack later
    Term &Postcondition = SynthFunCalls["pc"];
    Term &Invariant = SynthFunCalls["inv"];
    Term *LoopCond = MakeTerm(L->getLatchCmpInst(), Env);
    Term Exit = LoopCond->notTerm();
    // then make the updated arg vals for invariant
    std::vector<Term> NewArgs;
    DenseMap<Value *, Term> SysEnv;
    // sandbox everything in a totally new env
    for (auto *T : Terminals)
      SysEnv[Terms2Vals[T]] = UniversalVars[T];
    ExecuteOneIteration(LN, L, NewArgs, SysEnv,Loop2Converter);
    NewArgs.insert(NewArgs.begin(), SynthFuns["inv"]);
    LLVM_DEBUG(dbgs() << "NEW ARGS:\n");
    for (auto &A : NewArgs)
      LLVM_DEBUG(dbgs() << A.toString() << "\n");
    Term NewInv = slv.mkTerm(APPLY_UF, NewArgs);

    // then add constraints
    slv.addSygusAssume(slv.mkTerm(LT, {*MakeTerm(Terms2Vals[lb], SysEnv),
                                       *MakeTerm(Terms2Vals[ub], SysEnv)}));
    slv.addSygusConstraint(slv.mkTerm(IMPLIES, {Precondition, Invariant}));
    slv.addSygusConstraint(
        slv.mkTerm(IMPLIES, {slv.mkTerm(AND, {Invariant, *LoopCond}), NewInv}));
    slv.addSygusConstraint(slv.mkTerm(
        IMPLIES, {slv.mkTerm(AND, {Invariant, Exit}), Postcondition}));
    SynthResult res = slv.checkSynth();
    if (res.hasSolution()) {
      pc = slv.getSynthSolution(SynthFuns["pc"]);
      LLVM_DEBUG(dbgs() << "FOUND Postcondition:\n"
                        << pc.toString() << "\n");
      // also split all the equalities to a map, term* = term*
      FindValFromPC();
      // PC register should have one entry
      assert(PCRegister.size() == 1 && "expected one entry only");
    } else {
      LLVM_DEBUG(dbgs() << "no solution.\n");
    }
    slv.printStatisticsSafe(fileno(stdout));
  }

  void FindValFromPC() {
    assert(PCRegister.size() == 0 && "should be empty");
    std::function<void(Term&)> SearchTree;
    SearchTree = [this, &SearchTree](Term &Node) -> void {
      for (size_t i=0; i<Node.getNumChildren(); ++i) {
        if ((Node[i].getKind() == EQUAL
            || Node[i].getKind() == FLOATINGPOINT_EQ)
            && Node[i][0] == *liveout) {
          assert(Node[i].getNumChildren() == 2 && "incorrect node type");
          PCRegister.push_back({Node[i][0], Node[i][1]});
        } else {
          auto NextNode = Node[i];
          SearchTree(NextNode);
        }
      }
    };
    SearchTree(pc);
    assert(PCRegister.size() == 1 && "only one value should be found");
  }

  void ExecuteOneIteration(LoopNest *LN, Loop *L, std::vector<Term> &InvArgs,
                           DenseMap<Value *, Term> &Env, DenseMap<Loop *, CVCConv *> &Loop2Converter) {
    for (auto *NT : Terminals) {
      Term &UniVal = UniversalVars[NT];
      Value *V = Terms2Vals[NT];
      //      if (V == nullptr) {
      //        LLVM_DEBUG(dbgs() << "WARNING: creating new term for " <<
      //        NT->toString() << "\n"); Term *NV = MakeTerm(V, Env);
      //        Terms2Vals[NT] = V;
      //      }
      if (L->isLoopInvariant(V)) {
        InvArgs.push_back(UniVal);
        continue;
      }
      // otherwise, either Phi or load
      if (auto *PN = dyn_cast<PHINode>(V)) {
        if (PN->getParent() == L->getHeader()) {
          // for phi instructions, get the incoming (backedge) value
          Value *NextIter = PN->getIncomingValueForBlock(L->getLoopLatch());
          Term *NewVal = MakeTerm(NextIter, Env);
          InvArgs.push_back(*NewVal);
        } else {
          // Phi must be in separate latch block/somewhere else, and needs a value
          // from the depth+1-th loop
          // (1) find exit val for depth+1-th loop
          auto *Inner = LN->getLoopsAtDepth(L->getLoopDepth()+1)[0];
          CVCConv *InnerConv = Loop2Converter[Inner];
          SmallVector<BasicBlock *> ExitBlocks;
          Inner->getExitBlocks(ExitBlocks);
          assert(ExitBlocks.size() == 1 && "only one liveout allowed");

          // must be phi due to LCSSA form
          PHINode *Incoming = dyn_cast<PHINode>(PN->getIncomingValueForBlock(ExitBlocks[0]));

          if (InnerConv->liveoutend == Incoming->getIncomingValue(0)) {
            // (2) replace arg with matching PC of inner loop
//            Term EqualTo;
//            bool Found = false;
//            for (auto &P : InnerConv->PCRegister) {
//              if (P.first == InnerConv->liveout->toString()) {
//                EqualTo = P.second;
//                Found = true;
//                break;
//              }
//            }
//            assert(Found && "PC is missing from inner loop");
//
//            for (auto Elem : InnerConv->PCRegister)
//              LLVM_DEBUG(dbgs() << Elem.first << "\n" << Elem.second.toString() << "\n");
//            // (3) now have to convert all the parameters to the sygus vars
//            for (auto *NT2 : NonTerminals) {
//              Term &UV = UniversalVars[NT2];
//              EqualTo = EqualTo.substitute(*NT2, UV);
//            }
//            for (auto *NT2 : InnerConv->NonTerminals) {
//              Term &UV = InnerConv->UniversalVars[NT2];
//              EqualTo = EqualTo.substitute(*NT2, UV);
//            }
            InvArgs.push_back(*MakeTerm(PN, Env));
          } else {
            assert(0 && "the phi instruction must match the inner loop PC");
          }
        }
      } else if (auto *Load = dyn_cast<LoadInst>(V)) {
        assert(0 && "loads not supported yet");
      } else {
        assert(0 && "unsupported instruction");
      }
    }
  }

  void MakeTerminals(Loop *L, ScalarEvolution *SE, UFInfo &computechain,
                        DenseMap<Value *, Term> &Env) {
    SmallPtrSet<Term *, 8> NonTerms;

    auto Bounds = L->getBounds(*SE);
    auto *UB = &Bounds->getFinalIVValue();
    auto *LB = &Bounds->getInitialIVValue();
    auto *INDVAR = L->getInductionVariable(*SE);
    // also visit all the phis
    //    for (auto &I : *L->getHeader()) {
    //      if (!isa<PHINode>(&I))
    //        break;
    //      MakeTerm(&I, Env);
    //      RetrieveLeaves(&I, Env, NonTerms);
    //    }

    RetrieveLeaves(UB, Env, NonTerms);
    RetrieveLeaves(LB, Env, NonTerms);
    RetrieveLeaves(INDVAR, Env, NonTerms);
    for (auto *Arg : computechain.ArgVals)
      RetrieveLeaves(Arg, Env, NonTerms);
    //    auto BoundsLeaves = Leaves;
    //    Leaves.clear();
    // inject the lb and indvar into a special env
    //    DenseMap<Value*, Term> SpecialEnv;
    //    std::vector<Term> PostArgs;

    //    for (auto *V : computechain.ArgVals)
    //      PostArgs.push_back(*MakeTerm(V, Env));
    //    auto BoundVars = Leaves;
    //    // copy into non-ptr array
    //    for (auto T : BoundVars)
    //      if (T == indvar) continue ; // skip indvar
    //      else
    //        SumArgs.push_back(T);
    //    LLVM_DEBUG(dbgs() << "Created Sum Args:\n");
    //    for (auto &T : SumArgs)
    //      LLVM_DEBUG(dbgs() << T.toString() << "\n");

    NonTerms.insert(liveout);
    for (auto *T : NonTerms)
      Terminals.push_back(T);

    //    NonTerminals.push_back(indvar);
    //    for (auto *T : Leaves) NonTerminals.push_back(T);

    LLVM_DEBUG(dbgs() << "Created nonterminals:\n");
    for (auto &T : Terminals)
      LLVM_DEBUG(dbgs() << T->toString() << "\n");

    // create the reverse mapping
    for (auto &Elem : Env)
      Terms2Vals[&Elem.second] = Elem.first;

    //    Leaves = LeavesBackup;
  }

  Grammar MakeInvGram(UFInfo &computechain) {

    Term start = slv.mkVar(slv.getBooleanSort(), "start");
    Term cmp = slv.mkVar(slv.getBooleanSort(), "cmp");
    Term expr = slv.mkVar(slv.getIntegerSort(), "expr");
    Term eq = slv.mkVar(slv.getBooleanSort(), "eq");

    // construct grammar rules
    Term And = slv.mkTerm(AND, {cmp, cmp, eq});
    Term Leq = slv.mkTerm(LEQ, {expr, expr});
    cvc5::Kind EqKind =
        liveout->getKind() == CONST_FLOATINGPOINT ? FLOATINGPOINT_EQ : EQUAL;
    std::vector<Term> Args;
    Args.push_back(computechain.UF);
    Args.push_back(*lb);
    Args.push_back(slv.mkTerm(SUB, {*indvar, slv.mkInteger(1)}));
    for (auto *A : SumArgs)
      Args.push_back(*A);

    Term ComputeChain = slv.mkTerm(APPLY_UF, Args);
    Term equal = slv.mkTerm(EqKind, {*liveout, ComputeChain});

    std::vector<Term> BoundVars;
    for (auto *T : Terminals)
      BoundVars.push_back(*T);
    Grammar inv_gram = slv.mkGrammar(BoundVars, {start, cmp, expr, eq});

    inv_gram.addRules(start, {And});
    inv_gram.addRules(cmp, {Leq});
    inv_gram.addRules(expr, {*lb, *indvar, *ub});
    inv_gram.addRules(eq, {equal});

    LLVM_DEBUG(dbgs() << "INV GRAMMAR:\n");
    LLVM_DEBUG(dbgs() << inv_gram.toString() << "\n");

    return inv_gram;
  }

  Grammar MakePCGrammar(CVCConv::UFInfo compute_chain) {
    //    auto LeavesBackup = Leaves;
    //    Leaves.clear();
    //    DenseMap<Value*, Term> DummyEnv;
    ////    Term *ub = MakeTerm(UB, Env);
    ////    Term *lb = MakeTerm(LB, Env);
    //    auto BoundsLeaves = Leaves;
    //    Leaves.clear();
    //    // inject the lb and indvar into a special env
    //    DenseMap<Value*, Term> SpecialEnv;
    //    std::vector<Term> PostArgs;
    ////    Term indvar = MakeTerm(INDVAR, SpecialEnv);
    //    for (auto *V : compute_chain.ArgVals)
    //      PostArgs.push_back(MakeTerm(V, SpecialEnv));
    //    auto BoundVars = Leaves;
    //    // copy into non-ptr array
    //    std::vector<Term> BoundVars2;
    //    for (auto T : BoundVars)
    //      if (T == indvar) continue ; // skip indvar
    //      else BoundVars2.push_back(T);
    //    for (auto &T : BoundVars2)
    //      LLVM_DEBUG(dbgs() << T.toString() << "\n");

    Term start_pc = slv.mkVar(slv.getBooleanSort(), "start_pc");
    std::vector<Term> Args;

    Term ub_1 = slv.mkTerm(SUB, {*ub, slv.mkInteger(1)});
    Args.push_back(compute_chain.UF);
    Args.push_back(*lb);
    Args.push_back(ub_1);
    for (auto *A : SumArgs)
      Args.push_back(*A);

    Term sumpc = slv.mkTerm(APPLY_UF, Args);
    Term Eq1 = slv.mkTerm(EQUAL, {*indvar, *ub});
    auto EqKind = liveout->getSort() == fpsort ? FLOATINGPOINT_EQ : EQUAL;
    Term Eq2 = slv.mkTerm(EqKind, {*liveout, sumpc});
    Term AndPC = slv.mkTerm(AND, {Eq1, Eq2});
    // TODO make this general to handle non-sum cases

    //    std::vector<Term> Leaves2;
    //    for (auto T : BoundsLeaves) Leaves2.push_back(T);
    //    Leaves2.push_back(liveout);
    //    Leaves2.push_back(indvar);
    //    for (auto T : Leaves) Leaves2.push_back(T);
    std::vector<Term> BoundVars;
    for (auto *T : Terminals)
      BoundVars.push_back(*T);
    Grammar pc_gram = slv.mkGrammar(BoundVars, {start_pc});
    pc_gram.addRules(start_pc, {AndPC});

    LLVM_DEBUG(dbgs() << "PC GRAMMAR:\n");
    LLVM_DEBUG(dbgs() << pc_gram.toString() << "\n");

    //    Leaves = LeavesBackup;
    return pc_gram;
  }
};

//class Compression {
//  enum CType {
//      DENSE,
//      COMPRESSED
//  };
//  static isCompressed(Loop *L)
//};


PreservedAnalyses RevAnalysisPass::run(Function &F,
                                       FunctionAnalysisManager &AM) {
  errs() << F.getName() << "\n";

  auto start = high_resolution_clock::now();

  RecurrenceDescriptor RedDes;
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
  LoopAnnotations Annotate;
//  context c;
//  Z3Converter Conv(&c);
  LoopNest LN(*LI.getTopLevelLoops()[0], SE);
  DenseMap<Value *, std::string> LiveOutMap;

  // for each loop in the nest, inner to outer:
  //    1. find all liveins and liveouts
  //    2. create postcondition template: PC(liveins) = indvar = ub && liveout =
  //    <phi exit value or op_hole>
  //    3. create invariant template:     INV(liveins) = lb <= indvar <= ub &&
  //    liveout.store_target_or_phi = liveout.store_val_or_phi_exit
  //    4. are the templates complete?
  //        4.1 yes: map liveout to PC and go to next loop
  //        4.2 no : synthesize PC then map liveout to PC and go to next loop

  // PC grammar:
  // pc       := <indvar> == <ub> && <liveout> == <phi exit or op_hole>
  // indvar   := {any register in loop}
  // ub       := {any register in loop or int constant}
  // liveout  := {any register in exit blocks or store in loop}
  // lb       := {any register in loop or int constant}
  // op_hole  := sum(lb, ub, op_hole)
  //           | add(<op_hole>, <op_hole>) | sub | ...
  //           | cast(<op_hole>) | load(gep(<op_hole>, <op_hole>)) | ...
  //           | any register in loop | int constant | fp constant

  // TODO loop works for inner loop only right now, need to filter out the inner
  // loop BBs
//  DenseMap<Loop *, Term> Loop2PC;
  DenseMap<Loop *, CVCConv *> Loop2Converter;
  DenseMap<CVCConv *, DenseMap<Value *, Term>> Ins2TermsMap;
  DenseMap<Value *, Term> Ins2Terms;
  std::vector<std::tuple<Term, std::vector<Term>, Term>> FunctionBodies;

  for (int Depth = LN.getNestDepth(); Depth > 0; --Depth) {
    Loop *L = LN.getLoopsAtDepth(Depth)[0];
    // get live ins and live outs
//    SmallPtrSet<Value *, 4> LiveIns;
    SmallPtrSet<Value *, 4> LiveOuts;
//    GetLiveIns(L, LiveIns);
    GetLiveOuts(L, LiveOuts);
    assert(LiveOuts.size() == 1 && "only 1 output tensor supported for now");

    PHINode *IndVar = L->getInductionVariable(SE);
    LLVM_DEBUG(dbgs() << "Rev: Induction Variable is " << *IndVar << "\n");
    //    Solver slv;
    Loop2Converter[L] = new CVCConv;
    CVCConv *CConv = Loop2Converter[L];

//    Ins2TermsMap[CConv] = DenseMap<Value *, Term>();

    // Invariant inputs are just the induction var, lb, ub, + live ins
    //    SmallPtrSet<Value *, 6> InvariantInputs;
    //    InvariantInputs.insert(IndVar);
    //    InvariantInputs.insert(LiveIns.begin(), LiveIns.end());

    //    for (auto *V : InvariantInputs) {
    //      CConv.MakeTerm(V, Ins2Terms);
    //      LLVM_DEBUG(dbgs() << Ins2Terms[V].toString() << "\n");
    //    }
    //    LLVM_DEBUG(dbgs() << "LEAVES:\n");
    //    for (auto Leaf : CConv.Leaves) {
    //      LLVM_DEBUG(dbgs() << Leaf->toString() << "\n");
    //    }
    // check all the phis for reductions/inductions
    DenseMap<Value *, std::pair<RecurrenceDescriptor, PHINode *>> RecDecs;
    BasicBlock *Header = L->getHeader();
    for (auto &I : *Header) {
      if (auto *PN = dyn_cast<PHINode>(&I)) {
        RecurrenceDescriptor RecDec;
        if (RecurrenceDescriptor::isReductionPHI(PN, L, RecDec, &DB, &AC, &DT,
                                                 &SE)) {
          LLVM_DEBUG(dbgs() << "Rev: Reduction Instruction is "
                            << *(RecDec.getLoopExitInstr()) << "\n");
          RecDecs[RecDec.getLoopExitInstr()] = {RecDec, PN};
        }
      } else {
        break;
      }
    }

    // Then also get the live out
    Value *LLVMLiveOut = (*LiveOuts.begin());
    LLVM_DEBUG(dbgs() << "Rev: live out is " << *LLVMLiveOut << "\n");
    Value *LiveOutEnd = nullptr;
    if (isa<PHINode>(LLVMLiveOut)) {
      LLVMLiveOut = dyn_cast<PHINode>(LLVMLiveOut)->getOperand(0);
      if (RecDecs.count(LLVMLiveOut)) {
        // TODO: here there is one assumption about reduction, all the
        // computation are performed using one single instruction
        RecurrenceDescriptor &RD = RecDecs[LLVMLiveOut].first;
        LLVMLiveOut = RecDecs[LLVMLiveOut].second;
        LiveOutEnd =
            RD.getReductionOpChain(dyn_cast<PHINode>(LLVMLiveOut), L)[0];

        LLVM_DEBUG(dbgs() << "Rev: LiveOutEnd is " << *LiveOutEnd << "\n");
      }
      CConv->liveout = CConv->MakeTerm(LLVMLiveOut, Ins2Terms);
    } else // must be store
    {
      auto *Store = dyn_cast<StoreInst>(LLVMLiveOut);
      auto *GEP =
          dyn_cast<GEPOperator>(Store->getPointerOperand()); // get the GEP
      LLVMLiveOut = GEP->getPointerOperand(); // then get the base ptr
      LiveOutEnd = Store;
      // make the GEP:
      CConv->MakeTerm(GEP, Ins2Terms);
      // we only want the base
      CConv->liveout = &Ins2Terms[LLVMLiveOut];
    }
    CConv->liveoutend = LiveOutEnd;

    LLVM_DEBUG(dbgs() << "Rev: live out is " << CConv->liveout->toString()
                      << "\n");
    LLVM_DEBUG(dbgs() << "Rev: live out end is " << *(CConv->liveoutend)
                      << "\n");

    // Now, have to define the sum function for any phis
    // let's use a generic version and store it in CConv

    // Then have to create the postcondition/invariant grammar:
    // INV GRAMMAR:
    // start := (and <cmp> <cmp> <eq>))
    // cmp   := <expr> <= <expr>
    // expr  := lb | invariant | ub
    // eq    := {forall if eq is memory store} <single out> = <valid ops>
    // valid_ops :=
    //           | try to create sum from phi
    //           | + | - | * | ...

    // PC GRAMMAR:
    // start :=  (and <eq1>  ({forall if eq is memory store} <eq2>))
    // eq1      := lb == ub
    // eq2      := eq {where all phis have exit val}

    // find the loop bounds
    auto Bounds = L->getBounds(SE);
    auto *UB = &Bounds->getFinalIVValue();
    auto *LB = &Bounds->getInitialIVValue();
    auto *INDVAR = L->getInductionVariable(SE);
    CConv->ub = CConv->MakeTerm(UB, Ins2Terms);
    CConv->lb = CConv->MakeTerm(LB, Ins2Terms);
    CConv->indvar = CConv->MakeTerm(INDVAR, Ins2Terms);

    // translate the computation for the liveout
    CVCConv::UFInfo liveout_compute_chain =
        CConv->MakeComputeChain(FunctionBodies, LiveOutEnd, L, Ins2Terms, RecDecs);
    LLVM_DEBUG(dbgs() << "COMPUTE CHAIN:\n");
    LLVM_DEBUG(dbgs() << liveout_compute_chain.UF.toString() << "\n");

    CConv->MakeTerminals(L, &SE, liveout_compute_chain, Ins2Terms);

    auto inv_gram = CConv->MakeInvGram(liveout_compute_chain);

    // next, make the PC grammar
    Grammar pc_gram = CConv->MakePCGrammar(liveout_compute_chain);

    std::vector<CVCConv::GrammarRecord> GR = {{inv_gram, "inv"},
                                              {pc_gram, "pc"}};
    CConv->MakeSynthFuns(GR);
    CConv->MakeUniversalVars(GR);
    CConv->MakeSynthFunCalls();
    CConv->MakeVerificationConditions(&LN, L, Ins2Terms,Loop2Converter);

    // at this point, also need to figure out the mapping

  }

  // make a forest of possible replacements
  Term FinalPC;
  for (int Depth = LN.getNestDepth()-1; Depth > 0; --Depth) {
    Loop *Linner = LN.getLoopsAtDepth(Depth+1)[0];
    auto *Cinner = Loop2Converter[Linner];
    Loop *Louter = LN.getLoopsAtDepth(Depth)[0];
    auto *Couter = Loop2Converter[Louter];
    for (auto &P : Couter->PCRegister)
      if (P.first == *Couter->liveout) {
        FinalPC = P.second;
        auto *Inst = dyn_cast<Instruction>(Couter->liveoutend);
        SmallVector<BasicBlock*> ExitBlock;
        Linner->getExitBlocks(ExitBlock);
        for (auto &I : *ExitBlock[0]) {
          auto *PN = dyn_cast<PHINode>(&I);
          if (PN == nullptr || PN->getIncomingValue(0) != Cinner->liveoutend)
            break;
          for (auto *User : PN->users()) {
            FinalPC = FinalPC.substitute(*Couter->MakeTerm(User, Ins2Terms), Cinner->PCRegister[0].second);
          }
        }
        break;
      }
  }

  LLVM_DEBUG(dbgs() << "Final PC: " << FinalPC.toString() << "\n");
  // for now, just convert to z3
  // build a symbol table
  DenseMap<StringRef, Term> SymbolTable;
  for (auto &P : FunctionBodies)
    SymbolTable[std::get<0>(P).toString()] = std::get<2>(P);
  context c;
  // first convert all the functions
  Z3Mapping Mapping(c);
  for (auto &P : FunctionBodies) {
    std::vector<z3::sort> Domain;
    expr_vector &Args = Mapping.symbols();
    for (auto &E : std::get<1>(P))
      Domain.push_back(CVCSort2Z3Sort(E.getSort(), c));
    for (auto &E : std::get<1>(P)) {
      Args.push_back(CVC2Z3(Mapping, c, E));
    }
    z3::sort Range = CVCSort2Z3Sort(std::get<2>(P).getSort(), c);
    // make the signature
    Mapping.functions().push_back(c.recfun(
        std::get<0>(P).toString().c_str(),
        Domain.size(),
        Domain.data(),
        Range));
    LLVM_DEBUG(dbgs() << Mapping.functions().back().to_string() << "\n");
    Mapping.MakeMaps();
    auto Body = CVC2Z3(Mapping, c, std::get<2>(P));
    c.recdef(Mapping.functions().back(), Args, Body);
    LLVM_DEBUG(dbgs() << Body.to_string() << "\n");
  }

  expr Z3PC = CVC2Z3(Mapping, c, FinalPC);
  LLVM_DEBUG(dbgs() << Z3PC.to_string() << "\n");

  for (auto C : Loop2Converter)
    delete C.second;



  return PreservedAnalyses::all();

//  auto Depth = LN.getNestDepth();
//  for (; Depth > 0; --Depth) {
//    // first make partial Inv by equating all Phis
//    Loop *L = LN.getLoopsAtDepth(Depth)[0];
//    Optional<Loop::LoopBounds> Bounds = L->getBounds(SE);
//    for (auto &I : *L->getHeader()) {
//      auto *P = dyn_cast<PHINode>(&I);
//      if (P == nullptr)
//        break;
//      if (L->getInductionVariable(SE) == P) {
//        // Handle induction specially
//        //        Bounds->getInitialIVValue().printAsOperand(os);
//        auto lb = Conv.to_Z3(&Bounds->getInitialIVValue());
//        auto ub = Conv.to_Z3(&Bounds->getFinalIVValue());
//        auto indvar = Conv.to_Z3(P);
//        auto inv = (lb <= indvar) && (indvar <= ub);
//        //        Bounds->getFinalIVValue().printAsOperand(os);
//        Annotate.Loop2Inv[L].push_back(inv.to_string());
//        continue;
//      }
//      // otherwise, try to detect a recurrence
//      RecurrenceDescriptor Rec;
//      if (RecurrenceDescriptor::isReductionPHI(P, L, Rec, &DB, &AC, &DT, &SE)) {
//        // then describe in terms of the indvar and operation
//        auto *Result = Rec.getLoopExitInstr();
//        SmallVector<Instruction *> OpChain = Rec.getReductionOpChain(P, L);
//        // constraint: P == Result
//        //        expr Ps = c.real_const(P->getName().data());
//        //        expr Res = c.real_const(Result->getName().data());
//        std::string str;
//        std::string rstring;
//        raw_string_ostream resos(rstring);
//        raw_string_ostream os(str);
//        P->printAsOperand(os);
//        os << " == ";
//        resos << "Sum(";
//        Bounds->getInitialIVValue().printAsOperand(resos);
//        resos << ", " << L->getInductionVariable(SE)->getName() << " - 1, ";
//        OpChain[0]->print(resos);
//        resos << ")";
//        Annotate.Loop2Inv[L].push_back(str + rstring);
//        LiveOutMap[Result] = rstring;
//      } else {
//        // try another fallback method
//      }
//    }
//    LLVM_DEBUG(dbgs() << "Loop Invariants for " << L->getHeader()->getName()
//                      << "\n");
//    for (auto I : Annotate.Loop2Inv[L]) {
//      LLVM_DEBUG(dbgs() << "\t" << I << "\n");
//    }

    //    LiveInOut InOut(L);
    //    InOut.CollectLiveInOut();
    //    for (auto *I : InOut.LiveOut) {
    //      //    I->dump();
    //      StoreInst *Store;
    //      if ((Store = dyn_cast<StoreInst>(I))) {
    //        // is the store affine?
    //        auto *Ptr = SE.getSCEV(getLoadStorePointerOperand(Store));
    //        if (auto *Expr = dyn_cast<SCEVAddRecExpr>(Ptr)) {
    //          if (Expr->isAffine()) {
    //            std::string str;
    //            raw_string_ostream os(str);
    //            os << "affine write: ";
    //            getLoadStorePointerOperand(Store)->print(os, true);
    //            LLVM_DEBUG(dbgs() << str);
    //          } else {
    //            std::string str;
    //            raw_string_ostream os(str);
    //            os << "non-affine write: ";
    //            getLoadStorePointerOperand(Store)->print(os, true);
    //            LLVM_DEBUG(dbgs() << str);
    //          }
    //        } else {
    //          std::string str;
    //          raw_string_ostream os(str);
    //          os << "non-affine write: ";
    //          getLoadStorePointerOperand(Store)->print(os, true);
    //          LLVM_DEBUG(dbgs() << str);
    //        }
    //      }
    //    }
//  }
  // next find the post condition for the outer loop
  LiveInOut InOut(&LN.getOutermostLoop());
  InOut.CollectLiveInOut();
  assert(InOut.LiveOut.size() == 1 && "must be exactly 1 live out");
  // either a store or reg assignment
  if (auto *Store = dyn_cast<StoreInst>(*InOut.LiveOut.begin())) {
    auto *Ptr = dyn_cast<GEPOperator>(getLoadStorePointerOperand(Store));
    auto *ToStore = Store->getValueOperand();
    // go up def-use chain until a single instruction is found from a lower loop
    //    int Depth = 2;
    for (PHINode *TS; (TS = dyn_cast<PHINode>(ToStore));) {
      if (TS->getNumIncomingValues() == 1)
        ToStore = TS->getIncomingValue(0);
      else
        for (int i = 0; i < TS->getNumIncomingValues(); ++i) {
          if (!isa<PHINode>(TS->getIncomingValue(i)))
            continue;
          ToStore = TS->getIncomingValue(i);
        }
    }

    std::string str;
    raw_string_ostream os(str);
    os << "load(" << Ptr->getPointerOperand()->getName() << ", "
       << Ptr->getOperand(1)->getName() << ") == ";
    if (LiveOutMap.count(ToStore))
      os << LiveOutMap[ToStore];
    else
      ToStore->printAsOperand(os);
    Annotate.Postcondition.push_back(str);
  }

  LLVM_DEBUG(dbgs() << "Postcondition for " << LN.getOutermostLoop().getName()
                    << "\n");
  LLVM_DEBUG(dbgs() << "\t" << Annotate.Postcondition[0] << "\n");

  // Get Invariants by working backwards
  // SpMV CSR example:
  // 0. preprocessing
  //      for all loops, check the phis and find any recurrences
  //      inner loop: %sum.03 is a recurrence, generates %5
  //                  %k.02 is a recurrence, generates %idxprom6, %idxprom8
  //      outer loop: %i.o6 is a recurrence, generates %idxprom, %idxprom12
  //
  // Loop nest PC --> needs y[i]
  // y[i] gets it's value (store) from sum.0
  // sum.0 gets its value from .lcssa -> %5 -> check recurrences? generated by
  // %sum.03 y[i] in outer loop, %sum.03 in inner loop Inner invariant = (less
  // than i) && (= i) Outer invariant = (less than i) step 1: make partial Inv
  // for all loops
  //        partial Inv: phi instruction backedge == phi instruction header
  // step 2: make partial PC for outer loop
  //        live outs == PC(depth-1)

  return PreservedAnalyses::all();

  //  Loop *TheLoop = LI.getLoopsInPreorder()[1];
  //
  ////  auto &LAM =
  /// AM.getResult<LoopAnalysisManagerFunctionProxy>(F).getManager(); /  auto
  /// &AA = AM.getResult<AAManager>(F);
  ////
  //  auto *Module = F.getParent();
  ////  TargetLibraryInfoImpl TLII(Triple(Module->getTargetTriple()));
  ////  TargetLibraryInfo TLI(TLII);
  ////  TargetTransformInfo TTI(Module->getDataLayout());
  ////  LoopStandardAnalysisResults AR = {AA,  AC,  DT,      LI,      SE,
  ////                                    TLI, TTI, nullptr, nullptr, nullptr};
  ////  LoopNestAnalysis::Result LA = LAM.getResult<LoopNestAnalysis>(*TheLoop,
  /// AR);
  //
  //  // find sum phi
  //  PHINode *Phi = nullptr;
  //  for (auto &I : *TheLoop->getHeader())
  //    if (I.getName() == "sum.03" && (Phi = dyn_cast<PHINode>(&I)))
  //      break;
  //
  //  auto Sum = RecurrenceDescriptor::isReductionPHI(Phi, TheLoop, RedDes, &DB,
  //  &AC,
  //                                       &DT, &SE);
  //
  //  errs() << Sum << "\n";
  //
  //  // get start/end of inner loop
  //  InductionDescriptor IVDesc;
  //  TheLoop->getInductionDescriptor(SE, IVDesc);
  //
  //  //
  //
  //
  //  // The instruction who's value is used outside the loop.
  //  auto *LiveOut = RedDes.getLoopExitInstr();
  //  // Then find the store
  //  StoreInst *Store = nullptr;
  //  std::function<void(User*)> FindStore;
  //  FindStore = [&](User *User) {
  //    if (Store != nullptr) return;
  //    if ((Store = dyn_cast<StoreInst>(User))) return;
  //    for (auto *User2 : User->users()) FindStore(User2);
  //  };
  //
  //  for (auto *User : LiveOut->users()) FindStore(User);
  //
  //  // Two cases: loop is currently iterating, then
  //  // ( forall s s == i ) sum = sigma(l = rptr[i], k, val[l]*x[col[l]])
  //  auto *LowerBound = IVDesc.getStartValue();
  //  auto *CurrentUpper = TheLoop->getInductionVariable(SE);
  //  auto *Mul1 = LiveOut->getOperand(0);
  //  auto *Mul2 = LiveOut->getOperand(1);
  //
  //  std::string str;
  //  raw_string_ostream OS(str);
  //  auto *OuterIV = TheLoop->getParentLoop()->getInductionVariable(SE);
  //
  //  // now outer loop invariant:
  //  auto *OuterLoop = TheLoop->getParentLoop();
  //  // look for side-effects in outer loop (assume store for now):
  //  // find y array
  //  auto *Y =
  //  dyn_cast<GEPOperator>(getLoadStorePointerOperand(Store))->getOperand(0);
  //  auto *Rptr =
  //  dyn_cast<GEPOperator>(getLoadStorePointerOperand(LowerBound))->getOperand(0);
  //
  //  InductionDescriptor IVOuter;
  //  OuterLoop->getInductionDescriptor(SE, IVOuter);
  //
  //  auto stop = high_resolution_clock::now();
  //  auto duration = duration_cast<microseconds>(stop - start);
  //  errs() << "\n\n" << duration.count() << "\n\n";
  //
  //  OS << "forall s: ";
  //  IVOuter.getStartValue()->printAsOperand(OS, true, Module);
  //  OS << " <= s < " << OuterIV->getName() << " ==> " << Y->getName() << "[s]
  //  == " << Store->getValueOperand()->getName() << "\n"; std::string
  //  str_Outer(str); errs() << "\nOuterloop invariant:\n" << str; str.clear();
  //
  //
  //  OS << "forall s: s == " << OuterIV->getName() << " ==> " << Phi->getName()
  //  << " == sigma(l="; OS <<
  //  dyn_cast<GEPOperator>(getLoadStorePointerOperand(LowerBound))->getPointerOperand()->getName()
  //  << "[s]"; OS << ", " << CurrentUpper->getName() << ", ";
  //  Mul1->printAsOperand(OS, true, Module);
  //  OS << "*";
  //  Mul2->printAsOperand(OS, true, Module);
  //  OS << ")\n";
  //  errs() << "\nInnerloop invariant:\n" << str << "  and\n" << str_Outer;
  //
  //  // innerloop invariant = outerloop invariant + innerloop body invariant
  //
  //
  //
  //  auto *OuterUpperBound = OuterLoop->getLatchCmpInst()->getOperand(1);
  //
  //  str.clear();
  //  OS << "forall s: ";
  //  IVOuter.getStartValue()->printAsOperand(OS, true, Module);
  //  OS << " <= s < " << OuterUpperBound->getName() << " ==> " << Y->getName()
  //  << "[s] == " << Store->getValueOperand()->getName() << "\n"; OS << "  and
  //  " << OuterIV->getName() << " == " << OuterUpperBound->getName() << "\n";
  //  errs() << "\nPostcondition:\n" << str;
  //
  //
  //
  //  return PreservedAnalyses::all();
}