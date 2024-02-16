//
// Created by avery on 27/06/23.
//

#ifndef LLVM_REVPASS_H
#define LLVM_REVPASS_H

#include "llvm/IR/PassManager.h"

namespace llvm {

struct REVInfo {
  std::string OutStr;
};

class REVPass : public AnalysisInfoMixin<REVPass> {
  friend AnalysisInfoMixin<REVPass>;
  static AnalysisKey Key;
public:
  typedef REVInfo Result;
  REVInfo run(Function &F, FunctionAnalysisManager &AM);
};

} // namespace llvm

#endif // LLVM_REVPASS_H
