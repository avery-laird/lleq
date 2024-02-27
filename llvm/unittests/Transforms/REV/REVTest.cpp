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

#define REVTEST(functionName, filePath, expectedOut) TEST(REVTest, functionName) { \
  LLVMContext Ctx; \
  ModulePassManager MPM; \
  PassBuilder PB; \
  LoopAnalysisManager LAM; \
  FunctionAnalysisManager FAM; \
  CGSCCAnalysisManager CGAM; \
  ModuleAnalysisManager MAM; \
  PB.registerModuleAnalyses(MAM); \
  PB.registerCGSCCAnalyses(CGAM); \
  PB.registerFunctionAnalyses(FAM); \
  PB.registerLoopAnalyses(LAM); \
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM); \
  FAM.registerPass([&] { return REVPass(); }); \
  MAM.registerPass([&] { return FunctionAnalysisManagerModuleProxy(FAM); }); \
  SMDiagnostic Error; \
  std::unique_ptr<Module> M = parseAssemblyFile(filePath, Error, Ctx); \
  ASSERT_TRUE(M); \
  Function *F = M->getFunction(#functionName); \
  auto &REVOut = FAM.getResult<REVPass>(*F); \
  StringRef outStr = expectedOut; \
  EXPECT_STREQ(outStr.str().c_str(), REVOut.OutStr.c_str()); \
}

REVTEST(
    polybench_gemm,
    "/files/revpy/llvm-rev/llvm/unittests/Transforms/REV/polybench_gemm.ll",
    R"(%for.body3 = λ ptr 2 double %C, i32 %j.02 .
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
)")

REVTEST(
    DISABLED_taco_spmv_csc,
    "/files/revpy/analysis/taco_spmv_csc.ll",
    R"(%for.body5 = λ ptr 1 double %y_vals, i32 %iA.02 .
  %idxprom6 = sext i32 %iA.02 to i64
  %arrayidx7 = getelementptr inbounds i32, ptr %A2_crd, i64 %idxprom6
  %2 = load i32, ptr %arrayidx7, align 4
  %idxprom8 = sext i32 %2 to i64
  %arrayidx9 = getelementptr inbounds double, ptr %y_vals, i64 %idxprom8
  %3 = load double, ptr %arrayidx9, align 8
  %idxprom10 = sext i32 %iA.02 to i64
  %arrayidx11 = getelementptr inbounds double, ptr %A_vals, i64 %idxprom10
  %4 = load double, ptr %arrayidx11, align 8
  %idxprom12 = zext i32 %j.04 to i64
  %arrayidx13 = getelementptr inbounds double, ptr %x_vals, i64 %idxprom12
  %5 = load double, ptr %arrayidx13, align 8
  %6 = call double @llvm.fmuladd.f64(double %4, double %5, double %3)
  %idxprom14 = sext i32 %2 to i64
  %arrayidx15 = getelementptr inbounds double, ptr %y_vals, i64 %idxprom14
  %y_vals.1 =  store double %6, ptr %arrayidx15, align 8
  %inc = add nsw i32 %iA.02, 1
  %cmp4 = icmp slt i32 %inc, %7
(%y_vals.1) = fold (ptr 1 double %y_vals) %for.body5 Range(i32 %0, i32 %1)
%for.body5.dense = λ ptr 1 double %y_vals, i32 %iA.02.dense .
  %y_vals.elem = call double (ptr, i32, ...) @llvm.load.ptr(ptr %y_vals, i32 %iA.02.dense)
  %x_vals.elem = call double (ptr, i32, ...) @llvm.load.ptr(ptr %x_vals, i32 %j.04)
  %A_vals.dense.addr.mul = mul nsw i32 %iA.02.dense, %"7.dense"
  %A_vals.dense.addr.add = add nsw i32 %A_vals.dense.addr.mul, %j.04
  %A_vals.dense.gep = getelementptr inbounds double, ptr %A_vals.dense, i32 %A_vals.dense.addr.add
  %A_vals.dense.elem = load double, ptr %A_vals.dense.gep
  %"6.dense" = call double @llvm.fmuladd.f64(double %A_vals.dense.elem, double %x_vals.elem, double %y_vals.elem)
  %y_vals.addr = getelementptr inbounds double, ptr %y_vals, i32 %iA.02.dense
  %y_vals.1.dense =  store double %"6.dense", ptr %y_vals.addr, align 8
(%y_vals.1.dense) = fold (ptr 1 double %y_vals) %for.body5.dense Range(i32 0, i32 %"7.dense")
pos: (%0 = i32 %iA.02.dense, %1 = i32 %iA.02.dense)
crd: (%2 = i32 %iA.02.dense)
val: (%4 = double %A_vals.dense.elem)
%for.body = λ ptr 1 double %y_vals, i32 %j.04 .
  %idxprom = zext i32 %j.04 to i64
  %arrayidx = getelementptr inbounds i32, ptr %A2_pos, i64 %idxprom
  %0 = load i32, ptr %arrayidx, align 4
  %add = add nuw nsw i32 %j.04, 1
  %idxprom2 = zext i32 %add to i64
  %arrayidx3 = getelementptr inbounds i32, ptr %A2_pos, i64 %idxprom2
  %1 = load i32, ptr %arrayidx3, align 4
  %cmp41 = icmp slt i32 %0, %1
  %y_vals.3 = if ptr 1 double %cmp41 then %y_vals.1 else %y_vals
  %inc17 = add nuw nsw i32 %j.04, 1
  %cmp = icmp slt i32 %inc17, %x1_dimension
(%y_vals.3) = fold (ptr 1 double %y_vals) %for.body Range(i32 0, i32 %x1_dimension)
pos: ()
crd: ()
val: ()
)")

REVTEST(
    DISABLED_csparse_spmv_csc_nostruct,
    "/files/revpy/analysis/csparse_spmv_csc_nostruct.ll",
    R"(%for.body4 = λ ptr 1 double %y, i64 %p.02 .
  %arrayidx5 = getelementptr inbounds double, ptr %Ax, i64 %p.02
  %2 = load double, ptr %arrayidx5, align 8
  %arrayidx6 = getelementptr inbounds double, ptr %x, i64 %j.05
  %3 = load double, ptr %arrayidx6, align 8
  %arrayidx7 = getelementptr inbounds i64, ptr %Ai, i64 %p.02
  %4 = load i64, ptr %arrayidx7, align 8
  %arrayidx8 = getelementptr inbounds double, ptr %y, i64 %4
  %5 = load double, ptr %arrayidx8, align 8
  %6 = call double @llvm.fmuladd.f64(double %2, double %3, double %5)
  %y.1 =  store double %6, ptr %arrayidx8, align 8
(%y.1) = fold (ptr 1 double %y) %for.body4 Range(i64 %0, i64 %1)
%for.body4.dense = λ ptr 1 double %y, i64 %p.02.dense .
  %Ax.dense.addr.mul = mul nsw i64 %p.02.dense, %"7.dense"
  %Ax.dense.addr.add = add nsw i64 %Ax.dense.addr.mul, %j.05
  %Ax.dense.gep = getelementptr inbounds double, ptr %Ax.dense, i64 %Ax.dense.addr.add
  %Ax.dense.elem = load double, ptr %Ax.dense.gep
  %"3.dense" = call double (ptr, i64, ...) @llvm.load.ptr(ptr %x, i64 %j.05)
  %"5.dense" = call double (ptr, i64, ...) @llvm.load.ptr(ptr %y, i64 %p.02.dense)
  %"6.dense" = call double @llvm.fmuladd.f64(double %Ax.dense.elem, double %"3.dense", double %"5.dense")
  %y.addr = getelementptr inbounds double, ptr %y, i64 %p.02.dense
  %y.1.dense = store double %"6.dense", ptr %y.addr, align 8
(%y.1.dense) = fold (ptr 1 double %y) %for.body4.dense Range(i64 0, i64 %"7.dense")
pos: (%0 = i64 %p.02.dense, %1 = i64 %p.02.dense)
crd: (%4 = i64 %p.02.dense)
val: (%2 = double %Ax.dense.elem)
%for.body = λ ptr 1 double %y, i64 %j.05 .
  %arrayidx = getelementptr inbounds i64, ptr %Ap, i64 %j.05
  %0 = load i64, ptr %arrayidx, align 8
  %add = add nuw nsw i64 %j.05, 1
  %arrayidx2 = getelementptr inbounds i64, ptr %Ap, i64 %add
  %1 = load i64, ptr %arrayidx2, align 8
  %cmp31 = icmp slt i64 %0, %1
  %y.3 = if ptr 1 double %cmp31 then %y.1 else %y
  %inc10 = add nuw nsw i64 %j.05, 1
  %cmp = icmp slt i64 %inc10, %n
(%y.3) = fold (ptr 1 double %y) %for.body Range(i64 0, i64 %n)
pos: ()
crd: ()
val: ()
)")

REVTEST(
    SparseCompRow_matmult,
    "/files/revpy/analysis/SparseCompRow_matmult.ll",
    R"(%for.body8 = λ double %sum.03, i32 %i.02 .
  %idxprom9 = sext i32 %i.02 to i64
  %arrayidx10 = getelementptr inbounds i32, ptr %col, i64 %idxprom9
  %2 = load i32, ptr %arrayidx10, align 4
  %idxprom11 = sext i32 %2 to i64
  %arrayidx12 = getelementptr inbounds double, ptr %x, i64 %idxprom11
  %3 = load double, ptr %arrayidx12, align 8
  %arrayidx14 = getelementptr inbounds double, ptr %val, i64 %idxprom9
  %4 = load double, ptr %arrayidx14, align 8
  %5 = call double @llvm.fmuladd.f64(double %3, double %4, double %sum.03)
  %inc = add nsw i32 %i.02, 1
  %cmp7 = icmp slt i32 %inc, %1
(%5) = fold (double 0.000000e+00) %for.body8 Range(i32 %0, i32 %1)
%for.body8.dense = λ double %sum.03, i32 %i.02.dense .
  %idxprom9.dense = sext i32 %i.02.dense to i64
  %arrayidx10.dense = getelementptr inbounds i32, ptr %col, i64 %idxprom9.dense
  %"2.dense" = load i32, ptr %arrayidx10.dense, align 4
  %idxprom11.dense = sext i32 %"2.dense" to i64
  %arrayidx12.dense = getelementptr inbounds double, ptr %x, i64 %idxprom11.dense
  %x.elem = call addrspace(0) double (ptr, i32, ...) @llvm.load.ptr(ptr %x, i32 %i.02.dense)
  %arrayidx14.dense = getelementptr inbounds double, ptr %val, i64 %idxprom9.dense
  %val.dense.elem = call addrspace(0) double (ptr, i32, i32, ...) @llvm.load.ptr(ptr %val.dense, i32 %r.05, i32 %i.02.dense)
  %"5.dense" = call addrspace(0) double @llvm.fmuladd.f64(double %x.elem, double %val.dense.elem, double %sum.03)
  %inc.dense = add nsw i32 %i.02.dense, 1
  %cmp7.dense = icmp slt i32 %inc.dense, %1
  %"5.dense" = call addrspace(0) double @llvm.fmuladd.f64(double %x.elem, double %val.dense.elem, double %sum.03)
(%"5.dense") = fold (double 0.000000e+00) %for.body8 Range(i64 0, i32 %1.dense)
pos: ()
crd: (%2 = i32 %i.02.dense)
val: (%4 = double %val.dense.elem)
%for.body3 = λ ptr 1 double %y, i32 %r.05 .
  %idxprom = zext i32 %r.05 to i64
  %arrayidx = getelementptr inbounds i32, ptr %row, i64 %idxprom
  %0 = load i32, ptr %arrayidx, align 4
  %add = add nuw nsw i32 %r.05, 1
  %idxprom4 = zext i32 %add to i64
  %arrayidx5 = getelementptr inbounds i32, ptr %row, i64 %idxprom4
  %1 = load i32, ptr %arrayidx5, align 4
  %cmp71 = icmp slt i32 %0, %1
  %.lcssa = double %5
  %sum.0.lcssa = if double %cmp71 then %.lcssa else 0.000000e+00
  %arrayidx16 = getelementptr inbounds double, ptr %y, i64 %idxprom
  %6 = load double, ptr %arrayidx16, align 8
  %add17 = fadd double %6, %sum.0.lcssa
  %y.1 =  store double %add17, ptr %arrayidx16, align 8
  %cmp2 = icmp slt i32 %add, %M
(%y.1) = fold (ptr 1 double %y) %for.body3 Range(i32 0, i32 %M)
pos: (%row = i32 %r.05.dense)
crd: ()
val: ()
%for.body = λ ptr 1 double %y, i32 %reps.07 .
  %cmp24 = icmp sgt i32 %M, 0
  %y.3 = if ptr 1 double %cmp24 then %y.1 else %y
  %inc22 = add nuw nsw i32 %reps.07, 1
  %cmp = icmp slt i32 %inc22, %NUM_ITERATIONS
(%y.3) = fold (ptr 1 double %y) %for.body Range(i32 0, i32 %NUM_ITERATIONS)
pos: ()
crd: ()
val: ()
)")

REVTEST(
    spmv_npb,
    "/files/revpy/analysis/spmv_npb.ll",
    R"(%for.body6 = λ double %sum.03, i32 %k.02 .
  %idxprom7 = sext i32 %k.02 to i64
  %arrayidx8 = getelementptr inbounds double, ptr %a, i64 %idxprom7
  %2 = load double, ptr %arrayidx8, align 8
  %arrayidx10 = getelementptr inbounds i32, ptr %colidx, i64 %idxprom7
  %3 = load i32, ptr %arrayidx10, align 4
  %idxprom11 = sext i32 %3 to i64
  %arrayidx12 = getelementptr inbounds double, ptr %p, i64 %idxprom11
  %4 = load double, ptr %arrayidx12, align 8
  %5 = call double @llvm.fmuladd.f64(double %2, double %4, double %sum.03)
  %inc = add nsw i32 %k.02, 1
  %cmp5 = icmp slt i32 %inc, %1
(%5) = fold (double 0.000000e+00) %for.body6 Range(i32 %0, i32 %1)
%for.body6.dense = λ double %sum.03, i32 %k.02.dense .
  %idxprom7.dense = sext i32 %k.02.dense to i64
  %arrayidx8.dense = getelementptr inbounds double, ptr %a, i64 %idxprom7.dense
  %a.dense.elem = call addrspace(0) double (ptr, i32, i32, ...) @llvm.load.ptr(ptr %a.dense, i32 %j.05, i32 %k.02.dense)
  %arrayidx10.dense = getelementptr inbounds i32, ptr %colidx, i64 %idxprom7.dense
  %"3.dense" = load i32, ptr %arrayidx10.dense, align 4
  %idxprom11.dense = sext i32 %"3.dense" to i64
  %arrayidx12.dense = getelementptr inbounds double, ptr %p, i64 %idxprom11.dense
  %p.elem = call addrspace(0) double (ptr, i32, ...) @llvm.load.ptr(ptr %p, i32 %k.02.dense)
  %"5.dense" = call addrspace(0) double @llvm.fmuladd.f64(double %a.dense.elem, double %p.elem, double %sum.03)
  %inc.dense = add nsw i32 %k.02.dense, 1
  %cmp5.dense = icmp slt i32 %inc.dense, %1
  %"5.dense" = call addrspace(0) double @llvm.fmuladd.f64(double %a.dense.elem, double %p.elem, double %sum.03)
(%"5.dense") = fold (double 0.000000e+00) %for.body6 Range(i64 0, i32 %1.dense)
pos: ()
crd: (%3 = i32 %k.02.dense)
val: (%2 = double %a.dense.elem)
%for.body = λ ptr 1 double %q, i32 %j.05 .
  %idxprom = zext i32 %j.05 to i64
  %arrayidx = getelementptr inbounds i32, ptr %rowstr, i64 %idxprom
  %0 = load i32, ptr %arrayidx, align 4
  %add2 = add nuw nsw i32 %j.05, 1
  %idxprom3 = zext i32 %add2 to i64
  %arrayidx4 = getelementptr inbounds i32, ptr %rowstr, i64 %idxprom3
  %1 = load i32, ptr %arrayidx4, align 4
  %cmp51 = icmp slt i32 %0, %1
  %.lcssa = double %5
  %sum.0.lcssa = if double %cmp51 then %.lcssa else 0.000000e+00
  %arrayidx14 = getelementptr inbounds double, ptr %q, i64 %idxprom
  %q.1 =  store double %sum.0.lcssa, ptr %arrayidx14, align 8
  %cmp = icmp slt i32 %j.05, %sub
(%q.1) = fold (ptr 1 double %q) %for.body Range(i32 0, i32 %sub)
pos: (%rowstr = i32 %j.05.dense)
crd: ()
val: ()
)")

REVTEST(
    npb_is_hist,
    "/files/revpy/analysis/npb_is_hist.ll",
    R"(%for.body = λ ptr 1 i32 %work_buff, i32 %i.02 .
  %idxprom = zext i32 %i.02 to i64
  %arrayidx = getelementptr inbounds i32, ptr %key_buff_ptr2, i64 %idxprom
  %0 = load i32, ptr %arrayidx, align 4
  %idxprom1 = sext i32 %0 to i64
  %arrayidx2 = getelementptr inbounds i32, ptr %work_buff, i64 %idxprom1
  %1 = load i32, ptr %arrayidx2, align 4
  %inc = add nsw i32 %1, 1
  %work_buff.1 =  store i32 %inc, ptr %arrayidx2, align 4
  %inc3 = add nuw nsw i32 %i.02, 1
  %cmp = icmp slt i32 %inc3, %NUM_KEYS
(%work_buff.1) = fold (ptr 1 i32 %work_buff) %for.body Range(i32 0, i32 %NUM_KEYS)
pos: ()
crd: ()
val: ()
)")

REVTEST(
    parboil_hist,
    "/files/revpy/analysis/parboil_hist.ll",
    R"(%for.body13 = λ ptr 1 i8 %call4, i32 %i.02 .
  %idxprom = zext i32 %i.02 to i64
  %arrayidx = getelementptr inbounds i32, ptr %call, i64 %idxprom
  %0 = load i32, ptr %arrayidx, align 4
  %idxprom14 = zext i32 %0 to i64
  %arrayidx15 = getelementptr inbounds i8, ptr %call4, i64 %idxprom14
  %1 = load i8, ptr %arrayidx15, align 1
  %cmp17.not = icmp eq i8 %1, -1
  %inc = add i8 %1, 1
  %call4.4 =  store i8 %inc, ptr %arrayidx15, align 1
  %call4.5 = if ptr 1 i8 %cmp17.not then %call4.4 else %call4
  %inc21 = add i32 %i.02, 1
  %cmp11 = icmp ult i32 %inc21, %mul
(%call4.5) = fold (ptr 1 i8 %call4) %for.body13 Range(i32 0, i32 %mul)
pos: ()
crd: ()
val: ()
%for.body = λ ptr 1 i8 %call4, i32 %iter.04 .
  %call4.3 =  call void @llvm.memset.p0.i64(ptr align 1 %call4, i8 0, i64 %conv3, i1 false)
  %cmp111.not = icmp eq i32 %mul, 0
  %call4.7 = if ptr 1 i8 %cmp111.not then %call4.5 else %call4.3
  %inc23 = add nuw nsw i32 %iter.04, 1
  %cmp = icmp slt i32 %inc23, %numIterations
(%call4.7) = fold (ptr 1 i8 %call4.2) %for.body Range(i32 0, i32 %numIterations)
pos: ()
crd: ()
val: ()
)")

REVTEST(
    DISABLED_sparsebench_spmv_csr,
    "/files/revpy/analysis/sparsebench_spmv_csr.ll",
    R"(%for.body9 = λ double %sum.02, i32 %jrow.03 .
  %idxprom10 = sext i32 %jrow.03 to i64
  %arrayidx11 = getelementptr inbounds double, ptr %add.ptr2, i64 %idxprom10
  %3 = load double, ptr %arrayidx11, align 8
  %idxprom12 = sext i32 %jrow.03 to i64
  %arrayidx13 = getelementptr inbounds i32, ptr %add.ptr4, i64 %idxprom12
  %4 = load i32, ptr %arrayidx13, align 4
  %idxprom14 = sext i32 %4 to i64
  %arrayidx15 = getelementptr inbounds double, ptr %add.ptr, i64 %idxprom14
  %5 = load double, ptr %arrayidx15, align 8
  %6 = call double @llvm.fmuladd.f64(double %3, double %5, double %sum.02)
(%6) = fold (double 0.000000e+00) %for.body9 Range(i32 %1, i32 %2)
%for.body9.dense = λ double %sum.02, i32 %jrow.03.dense .
  %add.ptr.elem = call addrspace(0) double (ptr, i32, ...) @llvm.load.ptr(ptr %add.ptr, i32 %jrow.03.dense)
  %add.ptr2.dense.elem = call addrspace(0) double (ptr, i32, i32, ...) @llvm.load.ptr(ptr %add.ptr2, i32 %i.05, i32 %jrow.03.dense)
  %"6.dense" = call double @llvm.fmuladd.f64(double %add.ptr.elem, double %add.ptr2.dense.elem, double %sum.02)
(%"6.dense") = fold (double 0.000000e+00) %for.body9.dense Range(i32 0, i32 %"7.dense")
pos: ()
crd: (%4 = i32 %jrow.03.dense)
val: (%3 = double %add.ptr2.dense.elem)
%for.body = λ ptr 1 double %y, i32 %i.05 .
  %idxprom = zext i32 %i.05 to i64
  %arrayidx = getelementptr inbounds i32, ptr %ii, i64 %idxprom
  %1 = load i32, ptr %arrayidx, align 4
  %add = add nuw nsw i32 %i.05, 1
  %idxprom6 = zext i32 %add to i64
  %arrayidx7 = getelementptr inbounds i32, ptr %ii, i64 %idxprom6
  %2 = load i32, ptr %arrayidx7, align 4
  %cmp81 = icmp slt i32 %1, %2
  %.lcssa = double %6
  %sum.0.lcssa = if double %cmp81 then %.lcssa else 0.000000e+00
  %idxprom16 = zext i32 %i.05 to i64
  %arrayidx17 = getelementptr inbounds double, ptr %y, i64 %idxprom16
  %y.1 =  store double %sum.0.lcssa, ptr %arrayidx17, align 8
  %inc19 = add nuw nsw i32 %i.05, 1
  %cmp = icmp slt i32 %inc19, %0
(%y.1) = fold (ptr 1 double %y) %for.body Range(i32 0, i32 %0)
pos: (%ii = i64 %iv.dense)
crd: ()
val: ()
)")



//TEST(REVTest, PolybenchGEMM) {
//  // create pipeline
//  LLVMContext Ctx;
//  ModulePassManager MPM;
//  PassBuilder PB;
//  LoopAnalysisManager LAM;
//  FunctionAnalysisManager FAM;
//  CGSCCAnalysisManager CGAM;
//  ModuleAnalysisManager MAM;
//
//  PB.registerModuleAnalyses(MAM);
//  PB.registerCGSCCAnalyses(CGAM);
//  PB.registerFunctionAnalyses(FAM);
//  PB.registerLoopAnalyses(LAM);
//  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
//
//  FAM.registerPass([&] {return  REVPass(); });
//  MAM.registerPass([&] {return FunctionAnalysisManagerModuleProxy(FAM); });
//
//  SMDiagnostic Error;
//
//  std::unique_ptr<Module> M = parseAssemblyFile("/files/revpy/llvm-rev/llvm/unittests/Transforms/REV/polybench_gemm.ll", Error, Ctx);
//  ASSERT_TRUE(M);
//  Function *F = M->getFunction("polybench_gemm");
//
//  StringRef PolyBenchStr = R"(%for.body3 = λ ptr 2 double %C, i32 %j.02 .
//  %idxprom = zext i32 %i.09 to i64
//  %idxprom4 = zext i32 %j.02 to i64
//  %arrayidx5 = getelementptr inbounds [1100 x double], ptr %C, i64 %idxprom, i64 %idxprom4
//  %0 = load double, ptr %arrayidx5, align 8
//  %mul = fmul double %0, %beta
//  %C.1 =  store double %mul, ptr %arrayidx5, align 8
//  %inc = add nuw nsw i32 %j.02, 1
//  %cmp2 = icmp slt i32 %inc, %nj
//(%C.1) = fold (ptr 2 double %C) %for.body3 Range(i32 0, i32 %nj)
//pos: ()
//crd: ()
//val: ()
//%for.body11 = λ ptr 2 double %C, i32 %j.14 .
//  %idxprom12 = zext i32 %i.09 to i64
//  %idxprom14 = zext i32 %k.06 to i64
//  %arrayidx15 = getelementptr inbounds [1200 x double], ptr %A, i64 %idxprom12, i64 %idxprom14
//  %1 = load double, ptr %arrayidx15, align 8
//  %mul16 = fmul double %1, %alpha
//  %idxprom17 = zext i32 %k.06 to i64
//  %idxprom19 = zext i32 %j.14 to i64
//  %arrayidx20 = getelementptr inbounds [1100 x double], ptr %B, i64 %idxprom17, i64 %idxprom19
//  %2 = load double, ptr %arrayidx20, align 8
//  %idxprom22 = zext i32 %i.09 to i64
//  %idxprom24 = zext i32 %j.14 to i64
//  %arrayidx25 = getelementptr inbounds [1100 x double], ptr %C, i64 %idxprom22, i64 %idxprom24
//  %3 = load double, ptr %arrayidx25, align 8
//  %4 = call double @llvm.fmuladd.f64(double %mul16, double %2, double %3)
//  %C.2 =  store double %4, ptr %arrayidx25, align 8
//  %inc27 = add nuw nsw i32 %j.14, 1
//  %cmp10 = icmp slt i32 %inc27, %nj
//(%C.2) = fold (ptr 2 double %C) %for.body11 Range(i32 0, i32 %nj)
//pos: ()
//crd: ()
//val: ()
//%for.body8 = λ ptr 2 double %C, i32 %k.06 .
//  %cmp103 = icmp sgt i32 %nj, 0
//  %C.4 = if ptr 2 double %cmp103 then %C.2 else %C
//  %inc30 = add nuw nsw i32 %k.06, 1
//  %cmp7 = icmp slt i32 %inc30, %nk
//(%C.4) = fold (ptr 2 double %C.10) %for.body8 Range(i32 0, i32 %nk)
//pos: ()
//crd: ()
//val: ()
//%for.body = λ ptr 2 double %C, i32 %i.09 .
//  %cmp21 = icmp sgt i32 %nj, 0
//  %C.10 = if ptr 2 double %cmp21 then %C.1 else %C
//  %cmp75 = icmp sgt i32 %nk, 0
//  %C.6 = if ptr 2 double %cmp75 then %C.4 else %C.10
//  %inc33 = add nuw nsw i32 %i.09, 1
//  %cmp = icmp slt i32 %inc33, %ni
//(%C.6) = fold (ptr 2 double %C) %for.body Range(i32 0, i32 %ni)
//pos: ()
//crd: ()
//val: ()
//)";
//  auto &REVOut = FAM.getResult<REVPass>(*F);
//  EXPECT_STREQ(PolyBenchStr.str().c_str(), REVOut.OutStr.c_str());
//}

} // namespace
} // namespace llvm