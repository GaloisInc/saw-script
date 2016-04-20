; ModuleID = 'tmp/test.bc'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.st = type { i32, %union.anon }
%union.anon = type { %struct.inc_2_st }
%struct.inc_2_st = type { i32, i32 }
%struct.inc_1_st = type { i32 }

; Function Attrs: nounwind uwtable
define i32 @inc(%struct.st* %st) #0 {
  %1 = alloca i32, align 4
  %2 = alloca %struct.st*, align 8
  store %struct.st* %st, %struct.st** %2, align 8
  %3 = load %struct.st** %2, align 8
  %4 = getelementptr inbounds %struct.st* %3, i32 0, i32 0
  %5 = load i32* %4, align 4
  switch i32 %5, label %26 [
    i32 0, label %6
    i32 1, label %13
  ]

; <label>:6                                       ; preds = %0
  %7 = load %struct.st** %2, align 8
  %8 = getelementptr inbounds %struct.st* %7, i32 0, i32 1
  %9 = bitcast %union.anon* %8 to %struct.inc_1_st*
  %10 = getelementptr inbounds %struct.inc_1_st* %9, i32 0, i32 0
  %11 = load i32* %10, align 4
  %12 = add i32 %11, 1
  store i32 %12, i32* %10, align 4
  br label %27

; <label>:13                                      ; preds = %0
  %14 = load %struct.st** %2, align 8
  %15 = getelementptr inbounds %struct.st* %14, i32 0, i32 1
  %16 = bitcast %union.anon* %15 to %struct.inc_2_st*
  %17 = getelementptr inbounds %struct.inc_2_st* %16, i32 0, i32 0
  %18 = load i32* %17, align 4
  %19 = add i32 %18, 1
  store i32 %19, i32* %17, align 4
  %20 = load %struct.st** %2, align 8
  %21 = getelementptr inbounds %struct.st* %20, i32 0, i32 1
  %22 = bitcast %union.anon* %21 to %struct.inc_2_st*
  %23 = getelementptr inbounds %struct.inc_2_st* %22, i32 0, i32 1
  %24 = load i32* %23, align 4
  %25 = add i32 %24, 1
  store i32 %25, i32* %23, align 4
  br label %27

; <label>:26                                      ; preds = %0
  store i32 undef, i32* %1
  br label %28

; <label>:27                                      ; preds = %13, %6
  store i32 0, i32* %1
  br label %28

; <label>:28                                      ; preds = %27, %26
  %29 = load i32* %1
  ret i32 %29
}

attributes #0 = { nounwind uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.ident = !{!0}

!0 = !{!"Ubuntu clang version 3.6.2-1 (tags/RELEASE_362/final) (based on LLVM 3.6.2)"}
