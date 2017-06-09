; ModuleID = 'source.c'
source_filename = "source.c"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.12.0"

@example_sums.nums = private unnamed_addr constant [9 x i32] [i32 0, i32 1, i32 2, i32 3, i32 4, i32 6, i32 7, i32 8, i32 9], align 16

; Function Attrs: nounwind ssp uwtable
define i32 @identity(i32) #0 {
  %2 = alloca i32, align 4
  store i32 %0, i32* %2, align 4
  %3 = load i32, i32* %2, align 4
  ret i32 %3
}

; Function Attrs: nounwind ssp uwtable
define i32 @example() #0 {
  %1 = call i32 @identity(i32 1)
  %2 = call i32 @identity(i32 2)
  %3 = add nsw i32 %1, %2
  ret i32 %3
}

; Function Attrs: nounwind ssp uwtable
define i32 @bad_example() #0 {
  %1 = call i32 @identity(i32 3)
  ret i32 %1
}

; Function Attrs: nounwind ssp uwtable
define i32 @sum(i32*, i32) #0 {
  %3 = alloca i32*, align 8
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  store i32* %0, i32** %3, align 8
  store i32 %1, i32* %4, align 4
  store i32 0, i32* %5, align 4
  store i32 0, i32* %6, align 4
  br label %7

; <label>:7:                                      ; preds = %19, %2
  %8 = load i32, i32* %6, align 4
  %9 = load i32, i32* %4, align 4
  %10 = icmp slt i32 %8, %9
  br i1 %10, label %11, label %22

; <label>:11:                                     ; preds = %7
  %12 = load i32, i32* %6, align 4
  %13 = sext i32 %12 to i64
  %14 = load i32*, i32** %3, align 8
  %15 = getelementptr inbounds i32, i32* %14, i64 %13
  %16 = load i32, i32* %15, align 4
  %17 = load i32, i32* %5, align 4
  %18 = add nsw i32 %17, %16
  store i32 %18, i32* %5, align 4
  br label %19

; <label>:19:                                     ; preds = %11
  %20 = load i32, i32* %6, align 4
  %21 = add nsw i32 %20, 1
  store i32 %21, i32* %6, align 4
  br label %7

; <label>:22:                                     ; preds = %7
  %23 = load i32, i32* %5, align 4
  ret i32 %23
}

; Function Attrs: nounwind ssp uwtable
define i32 @example_sums() #0 {
  %1 = alloca [9 x i32], align 16
  %2 = bitcast [9 x i32]* %1 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* %2, i8* bitcast ([9 x i32]* @example_sums.nums to i8*), i64 36, i32 16, i1 false)
  %3 = getelementptr inbounds [9 x i32], [9 x i32]* %1, i32 0, i32 0
  %4 = call i32 @sum(i32* %3, i32 10)
  %5 = getelementptr inbounds [9 x i32], [9 x i32]* %1, i32 0, i32 0
  %6 = getelementptr inbounds i32, i32* %5, i64 2
  %7 = call i32 @sum(i32* %6, i32 6)
  %8 = add nsw i32 %4, %7
  ret i32 %8
}

; Function Attrs: argmemonly nounwind
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture writeonly, i8* nocapture readonly, i64, i32, i1) #1

attributes #0 = { nounwind ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"PIC Level", i32 2}
!1 = !{!"Apple LLVM version 8.1.0 (clang-802.0.42)"}
