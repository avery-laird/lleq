//
// Created by avery on 15/02/24.
//

#include "llvm/Analysis/REVPass.h"
//#include "llvm/Transforms/Utils/Mem2Reg.h"
//#include "llvm/Transforms/Scalar/LoopRotation.h"
//#include "llvm/Transforms/Scalar/LoopPassManager.h"
//#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/AsmParser/Parser.h"
#include "llvm/IR/Module.h"
#include "llvm/Passes/PassBuilder.h"
//#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Testing/Support/Error.h"
#include "gtest/gtest.h"

namespace llvm {
namespace {

TEST(REVTest, PolybenchGEMM) {
  // create pipeline
  LLVMContext Ctx;
  ModulePassManager MPM;
  PassBuilder PB;
  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;

  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  StringRef PipelineStr = "mem2reg,loop-rotate,instcombine,simplifycfg,loop-simplify,lcssa,revpass";
  ASSERT_THAT_ERROR(PB.parsePassPipeline(MPM, PipelineStr), Succeeded());

  SMDiagnostic Error;

  std::unique_ptr<Module> M = parseAssemblyFile("/files/revpy/llvm-rev/llvm/unittests/Transforms/REV/polybench_gemm.ll", Error, Ctx);
  ASSERT_TRUE(M);
  Function *F = M->getFunction("polybench_gemm");

  MPM.run(*M, MAM);

//  EXPECT_TRUE(true);
}

} // namespace
} // namespace llvm