//
// Created by avery on 2022-08-24.
//

#ifndef LLVM_REVANALYSIS_H
#define LLVM_REVANALYSIS_H

#include "DemandedBits.h"
#include "LoopNestAnalysis.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/PassManager.h"

namespace llvm {

class RevAnalysisPass : public PassInfoMixin<RevAnalysisPass> {

  enum LoopLevelFormat {
    // 0 -> n
    Dense,
    // rowptr[i] -> rowptr[i+1]
    Compressed,
    // other cases.
    Other
  };

  using LoopFormat = DenseMap<const Loop *, enum LoopLevelFormat>;

  LoopFormat LoopForm;

  bool LegalityAnalysis(Loop *TheLoop, LoopInfo *LI, ScalarEvolution *SE);
  void AnalyzeLoopBounds(Loop *L, Value *LowerBound, Value *UpperBound,
                         ScalarEvolution *SE);

  bool canSupportPhiInstrs(Loop *TheLoop, LoopInfo *LI,
                           DemandedBits *DB, AssumptionCache *AC,
                           DominatorTree *DT, ScalarEvolution *SE);

  void AnalyzeLoopStatements(LoopNest *LN, ScalarEvolution *SE);

public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_REVANALYSIS_H
