//
// Created by avery on 2022-08-24.
//

#ifndef LLVM_REVANALYSIS_H
#define LLVM_REVANALYSIS_H

#include "llvm/IR/PassManager.h"

namespace llvm {

class RevAnalysisPass : public PassInfoMixin<RevAnalysisPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_REVANALYSIS_H
