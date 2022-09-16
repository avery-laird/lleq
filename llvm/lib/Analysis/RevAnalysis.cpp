#include "llvm/Analysis/RevAnalysis.h"
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
#include "z3++.h"

#define DEBUG_TYPE "rev-analysis"

using namespace std::chrono;

using namespace llvm;
using namespace z3;

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

  return true;
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
  for (auto *LoopNest : LI.getTopLevelLoops()) {
    LLVM_DEBUG(dbgs() << " " << *LoopNest << "\n");
    if (!LegalityAnalysis(LoopNest, &LI, &SE)) {
      LLVM_DEBUG(dbgs() << "LLNA: "
                        << "fail to pass legality check \n");
      return PreservedAnalyses::all();
    }
  }

  // analysis here
  // live in/out: any scalars used outside the loop, or memory writes in the
  // loop
  LoopAnnotations Annotate;
  context c;

  LoopNest LN(*LI.getTopLevelLoops()[0], SE);
  DenseMap<Value *, std::string> LiveOutMap;
  auto Depth = LN.getNestDepth();
  for (; Depth > 0; --Depth) {
    // first make partial Inv by equating all Phis
    Loop *L = LN.getLoopsAtDepth(Depth)[0];
    Optional<Loop::LoopBounds> Bounds = L->getBounds(SE);
    for (auto &I : *L->getHeader()) {
      auto *P = dyn_cast<PHINode>(&I);
      if (P == nullptr)
        break;
      if (L->getInductionVariable(SE) == P) {
        // Handle induction specially
        std::string str;
        raw_string_ostream os(str);
        Bounds->getInitialIVValue().printAsOperand(os);
        os << " <= " << P->getName() << " <= ";
        Bounds->getFinalIVValue().printAsOperand(os);
        Annotate.Loop2Inv[L].push_back(str);
        continue;
      }
      // otherwise, try to detect a recurrence
      RecurrenceDescriptor Rec;
      if (RecurrenceDescriptor::isReductionPHI(P, L, Rec, &DB, &AC, &DT, &SE)) {
        // then describe in terms of the indvar and operation
        auto *Result = Rec.getLoopExitInstr();
        SmallVector<Instruction *> OpChain = Rec.getReductionOpChain(P, L);
        // constraint: P == Result
        expr Ps = c.real_const(P->getName().data());
        expr Res = c.real_const(Result->getName().data());
        std::string str;
        std::string rstring;
        raw_string_ostream resos(rstring);
        raw_string_ostream os(str);
        P->printAsOperand(os);
        os << " == ";
        resos << "Sum(";
        Bounds->getInitialIVValue().printAsOperand(resos);
        resos << ", " << L->getInductionVariable(SE)->getName() << " - 1, ";
        OpChain[0]->print(resos);
        resos << ")";
        Annotate.Loop2Inv[L].push_back(str + rstring);
        LiveOutMap[Result] = rstring;
      } else {
        // try another fallback method
      }
    }
    LLVM_DEBUG(dbgs() << "Loop Invariants for " << L->getHeader()->getName()
                      << "\n");
    for (auto I : Annotate.Loop2Inv[L]) {
      LLVM_DEBUG(dbgs() << "\t" << I << "\n");
    }

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
  }
  // next find the post condition for the outer loop
  LiveInOut InOut(&LN.getOutermostLoop());
  InOut.CollectLiveInOut();
  assert(InOut.LiveOut.size() == 1 && "must be exactly 1 live out");
  // either a store or reg assignment
  if (auto *Store = dyn_cast<StoreInst>(*InOut.LiveOut.begin())) {
    auto *Ptr = dyn_cast<GEPOperator>(getLoadStorePointerOperand(Store));
    auto *ToStore = Store->getValueOperand();
    // go up def-use chain until a single instruction is found from a lower loop
    int Depth = 2;
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