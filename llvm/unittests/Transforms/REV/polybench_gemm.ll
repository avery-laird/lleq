; ModuleID = '/files/revpy/ll/polybench_gemm.ll'
source_filename = "/files/revpy/benchmarks/polybench_gemm.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@.str = private unnamed_addr constant [1 x i8] zeroinitializer, align 1
@stderr = external global ptr, align 8
@.str.1 = private unnamed_addr constant [23 x i8] c"==BEGIN DUMP_ARRAYS==\0A\00", align 1
@.str.2 = private unnamed_addr constant [15 x i8] c"begin dump: %s\00", align 1
@.str.3 = private unnamed_addr constant [2 x i8] c"C\00", align 1
@.str.4 = private unnamed_addr constant [2 x i8] c"\0A\00", align 1
@.str.5 = private unnamed_addr constant [8 x i8] c"%0.2lf \00", align 1
@.str.6 = private unnamed_addr constant [17 x i8] c"\0Aend   dump: %s\0A\00", align 1
@.str.7 = private unnamed_addr constant [23 x i8] c"==END   DUMP_ARRAYS==\0A\00", align 1

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main(i32 noundef %argc, ptr noundef %argv) #0 {
entry:
  %alpha = alloca double, align 8
  %beta = alloca double, align 8
  %call = call ptr @polybench_alloc_data(i64 noundef 1100000, i32 noundef 8) #6
  %call1 = call ptr @polybench_alloc_data(i64 noundef 1200000, i32 noundef 8) #6
  %call2 = call ptr @polybench_alloc_data(i64 noundef 1320000, i32 noundef 8) #6
  call void @init_array(i32 noundef 1000, i32 noundef 1100, i32 noundef 1200, ptr noundef nonnull %alpha, ptr noundef nonnull %beta, ptr noundef %call, ptr noundef %call1, ptr noundef %call2)
  %0 = load double, ptr %alpha, align 8
  %1 = load double, ptr %beta, align 8
  call void @polybench_gemm(i32 noundef 1000, i32 noundef 1100, i32 noundef 1200, double noundef %0, double noundef %1, ptr noundef %call, ptr noundef %call1, ptr noundef %call2)
  %cmp = icmp sgt i32 %argc, 42
  br i1 %cmp, label %land.lhs.true, label %if.end

land.lhs.true:                                    ; preds = %entry
  %2 = load ptr, ptr %argv, align 8
  %strcmpload = load i8, ptr %2, align 1
  %tobool.not = icmp eq i8 %strcmpload, 0
  br i1 %tobool.not, label %if.then, label %if.end

if.then:                                          ; preds = %land.lhs.true
  call void @print_array(i32 noundef 1000, i32 noundef 1100, ptr noundef %call)
  br label %if.end

if.end:                                           ; preds = %if.then, %land.lhs.true, %entry
  call void @free(ptr noundef %call) #6
  call void @free(ptr noundef %call1) #6
  call void @free(ptr noundef %call2) #6
  ret i32 0
}

declare ptr @polybench_alloc_data(i64 noundef, i32 noundef) #1

; Function Attrs: noinline nounwind uwtable
define internal void @init_array(i32 noundef %ni, i32 noundef %nj, i32 noundef %nk, ptr noundef %alpha, ptr noundef %beta, ptr noundef %C, ptr noundef %A, ptr noundef %B) #0 {
entry:
  store double 1.500000e+00, ptr %alpha, align 8
  store double 1.200000e+00, ptr %beta, align 8
  %cmp3 = icmp sgt i32 %ni, 0
  br i1 %cmp3, label %for.body.preheader, label %for.end9

for.body.preheader:                               ; preds = %entry
  br label %for.body

for.body:                                         ; preds = %for.body.preheader, %for.inc7
  %i.04 = phi i32 [ %inc8, %for.inc7 ], [ 0, %for.body.preheader ]
  %cmp21 = icmp sgt i32 %nj, 0
  br i1 %cmp21, label %for.body3.preheader, label %for.inc7

for.body3.preheader:                              ; preds = %for.body
  br label %for.body3

for.body3:                                        ; preds = %for.body3.preheader, %for.body3
  %j.02 = phi i32 [ %inc, %for.body3 ], [ 0, %for.body3.preheader ]
  %mul = mul nsw i32 %i.04, %j.02
  %add = add nuw nsw i32 %mul, 1
  %rem = srem i32 %add, %ni
  %conv = sitofp i32 %rem to double
  %conv4 = sitofp i32 %ni to double
  %div = fdiv double %conv, %conv4
  %idxprom = zext i32 %i.04 to i64
  %idxprom5 = zext i32 %j.02 to i64
  %arrayidx6 = getelementptr inbounds [1100 x double], ptr %C, i64 %idxprom, i64 %idxprom5
  store double %div, ptr %arrayidx6, align 8
  %inc = add nuw nsw i32 %j.02, 1
  %cmp2 = icmp slt i32 %inc, %nj
  br i1 %cmp2, label %for.body3, label %for.inc7.loopexit, !llvm.loop !6

for.inc7.loopexit:                                ; preds = %for.body3
  br label %for.inc7

for.inc7:                                         ; preds = %for.inc7.loopexit, %for.body
  %inc8 = add nuw nsw i32 %i.04, 1
  %cmp = icmp slt i32 %inc8, %ni
  br i1 %cmp, label %for.body, label %for.end9.loopexit, !llvm.loop !8

for.end9.loopexit:                                ; preds = %for.inc7
  br label %for.end9

for.end9:                                         ; preds = %for.end9.loopexit, %entry
  %cmp117 = icmp sgt i32 %ni, 0
  br i1 %cmp117, label %for.body13.preheader, label %for.end33

for.body13.preheader:                             ; preds = %for.end9
  br label %for.body13

for.body13:                                       ; preds = %for.body13.preheader, %for.inc31
  %i.18 = phi i32 [ %inc32, %for.inc31 ], [ 0, %for.body13.preheader ]
  %cmp155 = icmp sgt i32 %nk, 0
  br i1 %cmp155, label %for.body17.preheader, label %for.inc31

for.body17.preheader:                             ; preds = %for.body13
  br label %for.body17

for.body17:                                       ; preds = %for.body17.preheader, %for.body17
  %j.16 = phi i32 [ %inc29, %for.body17 ], [ 0, %for.body17.preheader ]
  %add18 = add nuw nsw i32 %j.16, 1
  %mul19 = mul nsw i32 %i.18, %add18
  %rem20 = srem i32 %mul19, %nk
  %conv21 = sitofp i32 %rem20 to double
  %conv22 = sitofp i32 %nk to double
  %div23 = fdiv double %conv21, %conv22
  %idxprom24 = zext i32 %i.18 to i64
  %idxprom26 = zext i32 %j.16 to i64
  %arrayidx27 = getelementptr inbounds [1200 x double], ptr %A, i64 %idxprom24, i64 %idxprom26
  store double %div23, ptr %arrayidx27, align 8
  %inc29 = add nuw nsw i32 %j.16, 1
  %cmp15 = icmp slt i32 %inc29, %nk
  br i1 %cmp15, label %for.body17, label %for.inc31.loopexit, !llvm.loop !9

for.inc31.loopexit:                               ; preds = %for.body17
  br label %for.inc31

for.inc31:                                        ; preds = %for.inc31.loopexit, %for.body13
  %inc32 = add nuw nsw i32 %i.18, 1
  %cmp11 = icmp slt i32 %inc32, %ni
  br i1 %cmp11, label %for.body13, label %for.end33.loopexit, !llvm.loop !10

for.end33.loopexit:                               ; preds = %for.inc31
  br label %for.end33

for.end33:                                        ; preds = %for.end33.loopexit, %for.end9
  %cmp3511 = icmp sgt i32 %nk, 0
  br i1 %cmp3511, label %for.body37.preheader, label %for.end57

for.body37.preheader:                             ; preds = %for.end33
  br label %for.body37

for.body37:                                       ; preds = %for.body37.preheader, %for.inc55
  %i.212 = phi i32 [ %inc56, %for.inc55 ], [ 0, %for.body37.preheader ]
  %cmp399 = icmp sgt i32 %nj, 0
  br i1 %cmp399, label %for.body41.preheader, label %for.inc55

for.body41.preheader:                             ; preds = %for.body37
  br label %for.body41

for.body41:                                       ; preds = %for.body41.preheader, %for.body41
  %j.210 = phi i32 [ %inc53, %for.body41 ], [ 0, %for.body41.preheader ]
  %add42 = add nuw nsw i32 %j.210, 2
  %mul43 = mul nsw i32 %i.212, %add42
  %rem44 = srem i32 %mul43, %nj
  %conv45 = sitofp i32 %rem44 to double
  %conv46 = sitofp i32 %nj to double
  %div47 = fdiv double %conv45, %conv46
  %idxprom48 = zext i32 %i.212 to i64
  %idxprom50 = zext i32 %j.210 to i64
  %arrayidx51 = getelementptr inbounds [1100 x double], ptr %B, i64 %idxprom48, i64 %idxprom50
  store double %div47, ptr %arrayidx51, align 8
  %inc53 = add nuw nsw i32 %j.210, 1
  %cmp39 = icmp slt i32 %inc53, %nj
  br i1 %cmp39, label %for.body41, label %for.inc55.loopexit, !llvm.loop !11

for.inc55.loopexit:                               ; preds = %for.body41
  br label %for.inc55

for.inc55:                                        ; preds = %for.inc55.loopexit, %for.body37
  %inc56 = add nuw nsw i32 %i.212, 1
  %cmp35 = icmp slt i32 %inc56, %nk
  br i1 %cmp35, label %for.body37, label %for.end57.loopexit, !llvm.loop !12

for.end57.loopexit:                               ; preds = %for.inc55
  br label %for.end57

for.end57:                                        ; preds = %for.end57.loopexit, %for.end33
  ret void
}

; Function Attrs: noinline nounwind uwtable
define internal void @polybench_gemm(i32 noundef %ni, i32 noundef %nj, i32 noundef %nk, double noundef %alpha, double noundef %beta, ptr noundef %C, ptr noundef %A, ptr noundef %B) #0 {
entry:
  %cmp8 = icmp sgt i32 %ni, 0
  br i1 %cmp8, label %for.body.preheader, label %for.end34

for.body.preheader:                               ; preds = %entry
  br label %for.body

for.body:                                         ; preds = %for.body.preheader, %for.inc32
  %i.09 = phi i32 [ %inc33, %for.inc32 ], [ 0, %for.body.preheader ]
  %cmp21 = icmp sgt i32 %nj, 0
  br i1 %cmp21, label %for.body3.preheader, label %for.end

for.body3.preheader:                              ; preds = %for.body
  br label %for.body3

for.body3:                                        ; preds = %for.body3.preheader, %for.body3
  %j.02 = phi i32 [ %inc, %for.body3 ], [ 0, %for.body3.preheader ]
  %idxprom = zext i32 %i.09 to i64
  %idxprom4 = zext i32 %j.02 to i64
  %arrayidx5 = getelementptr inbounds [1100 x double], ptr %C, i64 %idxprom, i64 %idxprom4
  %0 = load double, ptr %arrayidx5, align 8
  %mul = fmul double %0, %beta
  store double %mul, ptr %arrayidx5, align 8
  %inc = add nuw nsw i32 %j.02, 1
  %cmp2 = icmp slt i32 %inc, %nj
  br i1 %cmp2, label %for.body3, label %for.end.loopexit, !llvm.loop !13

for.end.loopexit:                                 ; preds = %for.body3
  br label %for.end

for.end:                                          ; preds = %for.end.loopexit, %for.body
  %cmp75 = icmp sgt i32 %nk, 0
  br i1 %cmp75, label %for.body8.preheader, label %for.inc32

for.body8.preheader:                              ; preds = %for.end
  br label %for.body8

for.body8:                                        ; preds = %for.body8.preheader, %for.inc29
  %k.06 = phi i32 [ %inc30, %for.inc29 ], [ 0, %for.body8.preheader ]
  %cmp103 = icmp sgt i32 %nj, 0
  br i1 %cmp103, label %for.body11.preheader, label %for.inc29

for.body11.preheader:                             ; preds = %for.body8
  br label %for.body11

for.body11:                                       ; preds = %for.body11.preheader, %for.body11
  %j.14 = phi i32 [ %inc27, %for.body11 ], [ 0, %for.body11.preheader ]
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
  store double %4, ptr %arrayidx25, align 8
  %inc27 = add nuw nsw i32 %j.14, 1
  %cmp10 = icmp slt i32 %inc27, %nj
  br i1 %cmp10, label %for.body11, label %for.inc29.loopexit, !llvm.loop !14

for.inc29.loopexit:                               ; preds = %for.body11
  br label %for.inc29

for.inc29:                                        ; preds = %for.inc29.loopexit, %for.body8
  %inc30 = add nuw nsw i32 %k.06, 1
  %cmp7 = icmp slt i32 %inc30, %nk
  br i1 %cmp7, label %for.body8, label %for.inc32.loopexit, !llvm.loop !15

for.inc32.loopexit:                               ; preds = %for.inc29
  br label %for.inc32

for.inc32:                                        ; preds = %for.inc32.loopexit, %for.end
  %inc33 = add nuw nsw i32 %i.09, 1
  %cmp = icmp slt i32 %inc33, %ni
  br i1 %cmp, label %for.body, label %for.end34.loopexit, !llvm.loop !16

for.end34.loopexit:                               ; preds = %for.inc32
  br label %for.end34

for.end34:                                        ; preds = %for.end34.loopexit, %entry
  ret void
}

; Function Attrs: nounwind willreturn memory(read)
declare i32 @strcmp(ptr noundef, ptr noundef) #2

; Function Attrs: noinline nounwind uwtable
define internal void @print_array(i32 noundef %ni, i32 noundef %nj, ptr noundef %C) #0 {
entry:
  %0 = load ptr, ptr @stderr, align 8
  %1 = call i64 @fwrite(ptr nonnull @.str.1, i64 22, i64 1, ptr %0) #7
  %2 = load ptr, ptr @stderr, align 8
  %call1 = call i32 (ptr, ptr, ...) @fprintf(ptr noundef %2, ptr noundef nonnull @.str.2, ptr noundef nonnull @.str.3) #8
  %cmp4 = icmp sgt i32 %ni, 0
  br i1 %cmp4, label %for.body.preheader, label %for.end12

for.body.preheader:                               ; preds = %entry
  br label %for.body

for.body:                                         ; preds = %for.body.preheader, %for.inc10
  %i.05 = phi i32 [ %inc11, %for.inc10 ], [ 0, %for.body.preheader ]
  %cmp31 = icmp sgt i32 %nj, 0
  br i1 %cmp31, label %for.body4.preheader, label %for.inc10

for.body4.preheader:                              ; preds = %for.body
  br label %for.body4

for.body4:                                        ; preds = %for.body4.preheader, %if.end
  %j.02 = phi i32 [ %inc, %if.end ], [ 0, %for.body4.preheader ]
  %mul = mul nsw i32 %i.05, %ni
  %add = add nsw i32 %mul, %j.02
  %rem = srem i32 %add, 20
  %cmp5 = icmp eq i32 %rem, 0
  br i1 %cmp5, label %if.then, label %if.end

if.then:                                          ; preds = %for.body4
  %3 = load ptr, ptr @stderr, align 8
  %fputc = call i32 @fputc(i32 10, ptr %3)
  br label %if.end

if.end:                                           ; preds = %if.then, %for.body4
  %4 = load ptr, ptr @stderr, align 8
  %idxprom = zext i32 %i.05 to i64
  %idxprom7 = zext i32 %j.02 to i64
  %arrayidx8 = getelementptr inbounds [1100 x double], ptr %C, i64 %idxprom, i64 %idxprom7
  %5 = load double, ptr %arrayidx8, align 8
  %call9 = call i32 (ptr, ptr, ...) @fprintf(ptr noundef %4, ptr noundef nonnull @.str.5, double noundef %5) #8
  %inc = add nuw nsw i32 %j.02, 1
  %cmp3 = icmp slt i32 %inc, %nj
  br i1 %cmp3, label %for.body4, label %for.inc10.loopexit, !llvm.loop !17

for.inc10.loopexit:                               ; preds = %if.end
  br label %for.inc10

for.inc10:                                        ; preds = %for.inc10.loopexit, %for.body
  %inc11 = add nuw nsw i32 %i.05, 1
  %cmp = icmp slt i32 %inc11, %ni
  br i1 %cmp, label %for.body, label %for.end12.loopexit, !llvm.loop !18

for.end12.loopexit:                               ; preds = %for.inc10
  br label %for.end12

for.end12:                                        ; preds = %for.end12.loopexit, %entry
  %6 = load ptr, ptr @stderr, align 8
  %call13 = call i32 (ptr, ptr, ...) @fprintf(ptr noundef %6, ptr noundef nonnull @.str.6, ptr noundef nonnull @.str.3) #8
  %7 = load ptr, ptr @stderr, align 8
  %8 = call i64 @fwrite(ptr nonnull @.str.7, i64 22, i64 1, ptr %7) #7
  ret void
}

; Function Attrs: nounwind
declare void @free(ptr noundef) #3

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare double @llvm.fmuladd.f64(double, double, double) #4

declare i32 @fprintf(ptr noundef, ptr noundef, ...) #1

; Function Attrs: nofree nounwind
declare noundef i64 @fwrite(ptr nocapture noundef, i64 noundef, i64 noundef, ptr nocapture noundef) #5

; Function Attrs: nofree nounwind
declare noundef i32 @fputc(i32 noundef, ptr nocapture noundef) #5

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { nounwind willreturn memory(read) "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #5 = { nofree nounwind }
attributes #6 = { nounwind }
attributes #7 = { cold }
attributes #8 = { cold nounwind }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{!"clang version 17.0.0 (git@github.com:avery-laird/llvm-rev.git 1061946f2ab6266f3ebd79cea9e0cdf7a5789038)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}
!8 = distinct !{!8, !7}
!9 = distinct !{!9, !7}
!10 = distinct !{!10, !7}
!11 = distinct !{!11, !7}
!12 = distinct !{!12, !7}
!13 = distinct !{!13, !7}
!14 = distinct !{!14, !7}
!15 = distinct !{!15, !7}
!16 = distinct !{!16, !7}
!17 = distinct !{!17, !7}
!18 = distinct !{!18, !7}
