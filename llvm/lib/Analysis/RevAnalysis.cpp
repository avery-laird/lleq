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

#define DEBUG_TYPE "rev-analysis"

using namespace std::chrono;

using namespace llvm;

void AnalyzeLoopBounds(Loop *L, Value *LowerBound, Value *UpperBound,
                       ScalarEvolution *SE) {
  enum LoopLevelFormat { Dense, Compressed, Other };
  using LoopFormat = DenseMap<const Loop *, enum LoopLevelFormat>;

  LoopFormat Res;
}

bool LegalityAnalysis(Loop *TheLoop, LoopInfo *LI, ScalarEvolution *SE) {

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

    // Analyze the loop bound to obtain the property of loop at each level
  }

  int dim = 0;
  for (auto *Loop : TheLoop->getLoopsInPreorder()) {
    // 1 check bounds, affine or not?
    InductionDescriptor IVDesc;
    Loop->getInductionDescriptor(*SE, IVDesc);
    auto *Start = IVDesc.getStartValue();
    auto *End = Loop->getLatchCmpInst()->getOperand(1);
    errs() << "dim = " << dim++ << "\n";
    // check dense
    if (dyn_cast<ConstantInt>(Start) &&
        (dyn_cast<ConstantInt>(End) || dyn_cast<Argument>(End)))
      errs() << "maybe dense or compressed (unordered)\n";
    if (dyn_cast<LoadInst>(Start) && dyn_cast<LoadInst>(End))
      if (isa<GEPOperator>(getPointerOperand(Start)) &&
          isa<GEPOperator>(getPointerOperand(End)))
        errs() << "maybe compressed\n";
  }

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
      SmallVector<BasicBlock*> ExitBlocks;
      L->getExitBlocks(ExitBlocks);
      for (auto *BB : ExitBlocks)
        for (auto &I : *BB) {
          PHINode *Phi = dyn_cast<PHINode>(&I);
          assert(Phi && Phi->getNumIncomingValues() == 1 && "loop should be in LCSSA");
          LiveOut.insert(Phi->getIncomingValue(0));
        }

    for (auto *I : WorkList) {
        if (!L->contains(I))
          LiveOut.insert(I);
    }
  }
};

PreservedAnalyses RevAnalysisPass::run(Function &F,
                                       FunctionAnalysisManager &AM) {
  errs() << F.getName() << "\n";

  auto start = high_resolution_clock::now();

  RecurrenceDescriptor RedDes;
  AssumptionCache AC = AM.getResult<AssumptionAnalysis>(F);
  DominatorTree &DT = AM.getResult<DominatorTreeAnalysis>(F);
  DemandedBits DB(F, AC, DT);

  LoopInfo &LI = AM.getResult<LoopAnalysis>(F);
  ScalarEvolution &SE = AM.getResult<ScalarEvolutionAnalysis>(F);
  for (auto *LoopNest : LI.getTopLevelLoops()) {
    LLVM_DEBUG(dbgs() << " " << *LoopNest << "\n");
    if (!LegalityAnalysis(LoopNest, &LI, &SE))
      return PreservedAnalyses::all();
  }

  // analysis here
  // live in/out: any scalars used outside the loop, or memory writes in the
  // loop

  LoopNest LN(*LI.getTopLevelLoops()[0], SE);
  auto Depth = LN.getNestDepth();
  for (; Depth >= 0; --Depth) {
    LiveInOut InOut(LN.getLoopsAtDepth(Depth)[0]);
    InOut.CollectLiveInOut();
    for (auto *I : InOut.LiveOut) {
      //    I->dump();
      StoreInst *Store;
      if ((Store = dyn_cast<StoreInst>(I))) {
        // is the store affine?
        auto *Ptr = SE.getSCEV(getLoadStorePointerOperand(Store));
        if (auto *Expr = dyn_cast<SCEVAddRecExpr>(Ptr)) {
          if (Expr->isAffine()) {
            std::string str;
            raw_string_ostream os(str);
            os << "affine write: ";
            getLoadStorePointerOperand(Store)->print(os, true);
            LLVM_DEBUG(dbgs() << str);
          } else {
            std::string str;
            raw_string_ostream os(str);
            os << "non-affine write: ";
            getLoadStorePointerOperand(Store)->print(os, true);
            LLVM_DEBUG(dbgs() << str);
          }
        } else {
          std::string str;
          raw_string_ostream os(str);
          os << "non-affine write: ";
          getLoadStorePointerOperand(Store)->print(os, true);
          LLVM_DEBUG(dbgs() << str);
        }
      }
    }
  }

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
  // sum.0 gets its value from .lcssa -> %5 -> check recurrences? generated by %sum.03
  // y[i] in outer loop, %sum.03 in inner loop
  // Inner invariant = (less than i) && (= i)
  // Outer invariant = (less than i)

  return PreservedAnalyses::all();

  //  Loop *TheLoop = LI.getLoopsInPreorder()[1];
  //
  ////  auto &LAM =
  ///AM.getResult<LoopAnalysisManagerFunctionProxy>(F).getManager(); /  auto &AA
  ///= AM.getResult<AAManager>(F);
  ////
  //  auto *Module = F.getParent();
  ////  TargetLibraryInfoImpl TLII(Triple(Module->getTargetTriple()));
  ////  TargetLibraryInfo TLI(TLII);
  ////  TargetTransformInfo TTI(Module->getDataLayout());
  ////  LoopStandardAnalysisResults AR = {AA,  AC,  DT,      LI,      SE,
  ////                                    TLI, TTI, nullptr, nullptr, nullptr};
  ////  LoopNestAnalysis::Result LA = LAM.getResult<LoopNestAnalysis>(*TheLoop,
  ///AR);
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