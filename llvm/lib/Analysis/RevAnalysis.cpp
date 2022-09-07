#include "llvm/Analysis/RevAnalysis.h"
#include "llvm/Analysis/IVDescriptors.h"
#include "llvm/Analysis/DemandedBits.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/LoopNestAnalysis.h"
#include "llvm/Analysis/LoopAccessAnalysis.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/ADT/Triple.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/raw_ostream.h"
#include <chrono>
using namespace std::chrono;



using namespace llvm;


bool LegalityAnalysis(Function *F, LoopInfo *LI, ScalarEvolution *SE) {
  auto Loops = LI->getLoopsInPreorder();
  if (Loops.size() > 2)
    return false;
  int dim = 0;
  for (auto *Loop : Loops) {
    // 1 check bounds, affine or not?
    InductionDescriptor IVDesc;
    Loop->getInductionDescriptor(*SE, IVDesc);
    auto *Start = IVDesc.getStartValue();
    auto *End = Loop->getLatchCmpInst()->getOperand(1);
    errs() << "dim = " << dim++ << "\n";
    // check dense
    if (dyn_cast<ConstantInt>(Start) && (dyn_cast<ConstantInt>(End) || dyn_cast<Argument>(End)))
      errs() << "maybe dense or compressed (unordered)\n";
    if (dyn_cast<LoadInst>(Start) && dyn_cast<LoadInst>(End))
      if (isa<GEPOperator>(getPointerOperand(Start)) && isa<GEPOperator>(getPointerOperand(End)))
        errs() << "maybe compressed\n";
  }

  return true;
}

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
  if (!LegalityAnalysis(&F, &LI, &SE))
    return PreservedAnalyses::all();

  // analysis here

  return PreservedAnalyses::all();


//  Loop *TheLoop = LI.getLoopsInPreorder()[1];
//
////  auto &LAM = AM.getResult<LoopAnalysisManagerFunctionProxy>(F).getManager();
////  auto &AA = AM.getResult<AAManager>(F);
////
//  auto *Module = F.getParent();
////  TargetLibraryInfoImpl TLII(Triple(Module->getTargetTriple()));
////  TargetLibraryInfo TLI(TLII);
////  TargetTransformInfo TTI(Module->getDataLayout());
////  LoopStandardAnalysisResults AR = {AA,  AC,  DT,      LI,      SE,
////                                    TLI, TTI, nullptr, nullptr, nullptr};
////  LoopNestAnalysis::Result LA = LAM.getResult<LoopNestAnalysis>(*TheLoop, AR);
//
//  // find sum phi
//  PHINode *Phi = nullptr;
//  for (auto &I : *TheLoop->getHeader())
//    if (I.getName() == "sum.03" && (Phi = dyn_cast<PHINode>(&I)))
//      break;
//
//  auto Sum = RecurrenceDescriptor::isReductionPHI(Phi, TheLoop, RedDes, &DB, &AC,
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
//  auto *Y = dyn_cast<GEPOperator>(getLoadStorePointerOperand(Store))->getOperand(0);
//  auto *Rptr = dyn_cast<GEPOperator>(getLoadStorePointerOperand(LowerBound))->getOperand(0);
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
//  OS << " <= s < " << OuterIV->getName() << " ==> " << Y->getName() << "[s] == " << Store->getValueOperand()->getName() << "\n";
//  std::string str_Outer(str);
//  errs() << "\nOuterloop invariant:\n" << str;
//  str.clear();
//
//
//  OS << "forall s: s == " << OuterIV->getName() << " ==> " << Phi->getName() << " == sigma(l=";
//  OS << dyn_cast<GEPOperator>(getLoadStorePointerOperand(LowerBound))->getPointerOperand()->getName() << "[s]";
//  OS << ", " << CurrentUpper->getName() << ", ";
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
//  OS << " <= s < " << OuterUpperBound->getName() << " ==> " << Y->getName() << "[s] == " << Store->getValueOperand()->getName() << "\n";
//  OS << "  and " << OuterIV->getName() << " == " << OuterUpperBound->getName() << "\n";
//  errs() << "\nPostcondition:\n" << str;
//
//
//
//  return PreservedAnalyses::all();
}