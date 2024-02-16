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

//  StringRef PipelineStr = "mem2reg,loop-rotate,instcombine,simplifycfg,loop-simplify,lcssa,revpass";
//  StringRef PipelineStr = "revpass";
//  ASSERT_THAT_ERROR(PB.parsePassPipeline(MPM, PipelineStr), Succeeded());

  FAM.registerPass([&] {return  REVPass(); });
  MAM.registerPass([&] {return FunctionAnalysisManagerModuleProxy(FAM); });


  SMDiagnostic Error;

  std::unique_ptr<Module> M = parseAssemblyFile("/files/revpy/llvm-rev/llvm/unittests/Transforms/REV/polybench_gemm.ll", Error, Ctx);
  ASSERT_TRUE(M);
  Function *F = M->getFunction("polybench_gemm");

  StringRef PolyBenchStr = R"(%for.body3 = λ ptr 2 double %C, i32 %j.02 .
  %idxprom = zext i32 %i.09 to i64
  %idxprom4 = zext i32 %j.02 to i64
  %arrayidx5 = getelementptr inbounds [1100 x double], ptr %C, i64 %idxprom, i64 %idxprom4
  %0 = load double, ptr %arrayidx5, align 8
  %mul = fmul double %0, %beta
  %C.1 =  store double %mul, ptr %arrayidx5, align 8
  %inc = add nuw nsw i32 %j.02, 1
  %cmp2 = icmp slt i32 %inc, %nj
(%C.1) = fold (ptr 2 double %C) %for.body3 Range(i32 0, i32 %nj)
pos: ()
crd: ()
val: ()
%for.body11 = λ ptr 2 double %C, i32 %j.14 .
  %idxprom12 = zext i32 %i.09 to i64
  %idxprom14 = zext i32 %k.06 to i64
  %arrayidx15 = getelementptr inbounds [1200 x double], ptr %A, i64 %idxprom12, i64 %idxprom14
  %1 = load double, ptr %arrayidx15, align 8
  %mul16 = fmul double %1, %alpha
  %idxprom17 = zext i32 %k.06 to i64
  %idxprom19 = zext i32 %j.14 to i64
  %arrayidx20 = getelementptr inbounds [1100 x double], ptr %B, i64 %idxprom17, i64 %idxprom19
  %2 = load double, ptr %arrayidx20, align 8
  %idxprom22 = zext i32 %i.09 to i64
  %idxprom24 = zext i32 %j.14 to i64
  %arrayidx25 = getelementptr inbounds [1100 x double], ptr %C, i64 %idxprom22, i64 %idxprom24
  %3 = load double, ptr %arrayidx25, align 8
  %4 = call double @llvm.fmuladd.f64(double %mul16, double %2, double %3)
  %C.2 =  store double %4, ptr %arrayidx25, align 8
  %inc27 = add nuw nsw i32 %j.14, 1
  %cmp10 = icmp slt i32 %inc27, %nj
(%C.2) = fold (ptr 2 double %C) %for.body11 Range(i32 0, i32 %nj)
pos: ()
crd: ()
val: ()
%for.body8 = λ ptr 2 double %C, i32 %k.06 .
  %cmp103 = icmp sgt i32 %nj, 0
  %C.4 = if ptr 2 double %cmp103 then %C.2 else %C
  %inc30 = add nuw nsw i32 %k.06, 1
  %cmp7 = icmp slt i32 %inc30, %nk
(%C.4) = fold (ptr 2 double %C.10) %for.body8 Range(i32 0, i32 %nk)
pos: ()
crd: ()
val: ()
%for.body = λ ptr 2 double %C, i32 %i.09 .
  %cmp21 = icmp sgt i32 %nj, 0
  %C.10 = if ptr 2 double %cmp21 then %C.1 else %C
  %cmp75 = icmp sgt i32 %nk, 0
  %C.6 = if ptr 2 double %cmp75 then %C.4 else %C.10
  %inc33 = add nuw nsw i32 %i.09, 1
  %cmp = icmp slt i32 %inc33, %ni
(%C.6) = fold (ptr 2 double %C) %for.body Range(i32 0, i32 %ni)
pos: ()
crd: ()
val: ()
)";

//  MPM.run(*M, MAM);
  auto &REVOut = FAM.getResult<REVPass>(*F);
//  outs() << REVOut.OutStr;
  EXPECT_STREQ(PolyBenchStr.str().c_str(), REVOut.OutStr.c_str());

//  EXPECT_TRUE(true);
}

} // namespace
} // namespace llvm