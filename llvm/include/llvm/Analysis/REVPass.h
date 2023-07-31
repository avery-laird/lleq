//
// Created by avery on 27/06/23.
//

#ifndef LLVM_REVPASS_H
#define LLVM_REVPASS_H

#include "llvm/IR/PassManager.h"

namespace llvm {

class REVPass : public PassInfoMixin<REVPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_REVPASS_H
