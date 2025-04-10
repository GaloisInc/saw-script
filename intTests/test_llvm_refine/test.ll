; ModuleID = 'test.c'
source_filename = "test.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx11.0.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @f(i32 %0) #0 !dbg !9 {
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 %0, i32* %3, align 4
  call void @llvm.dbg.declare(metadata i32* %3, metadata !13, metadata !DIExpression()), !dbg !14
  %4 = load i32, i32* %3, align 4, !dbg !15
  switch i32 %4, label %9 [
    i32 2, label %5
    i32 4, label %6
    i32 8, label %7
    i32 16, label %8
  ], !dbg !16

5:                                                ; preds = %1
  store i32 1, i32* %2, align 4, !dbg !17
  br label %10, !dbg !17

6:                                                ; preds = %1
  store i32 2, i32* %2, align 4, !dbg !19
  br label %10, !dbg !19

7:                                                ; preds = %1
  store i32 3, i32* %2, align 4, !dbg !20
  br label %10, !dbg !20

8:                                                ; preds = %1
  store i32 4, i32* %2, align 4, !dbg !21
  br label %10, !dbg !21

9:                                                ; preds = %1
  store i32 0, i32* %2, align 4, !dbg !22
  br label %10, !dbg !22

10:                                               ; preds = %9, %8, %7, %6, %5
  %11 = load i32, i32* %2, align 4, !dbg !23
  ret i32 %11, !dbg !23
}

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "darwin-stkchk-strong-link" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "probe-stack"="___chkstk_darwin" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable willreturn }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.dbg.cu = !{!5}
!llvm.ident = !{!8}

!0 = !{i32 2, !"SDK Version", [2 x i32] [i32 12, i32 1]}
!1 = !{i32 7, !"Dwarf Version", i32 4}
!2 = !{i32 2, !"Debug Info Version", i32 3}
!3 = !{i32 1, !"wchar_size", i32 4}
!4 = !{i32 7, !"PIC Level", i32 2}
!5 = distinct !DICompileUnit(language: DW_LANG_C99, file: !6, producer: "Apple clang version 12.0.5 (clang-1205.0.22.11)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !7, nameTableKind: None, sysroot: "/Library/Developer/CommandLineTools/SDKs/MacOSX12.1.sdk", sdk: "MacOSX12.1.sdk")
!6 = !DIFile(filename: "test.c", directory: "/Users/rdockins/code/saw-script/intTests/test_llvm_refine")
!7 = !{}
!8 = !{!"Apple clang version 12.0.5 (clang-1205.0.22.11)"}
!9 = distinct !DISubprogram(name: "f", scope: !6, file: !6, line: 2, type: !10, scopeLine: 3, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, retainedNodes: !7)
!10 = !DISubroutineType(types: !11)
!11 = !{!12, !12}
!12 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!13 = !DILocalVariable(name: "i", arg: 1, scope: !9, file: !6, line: 2, type: !12)
!14 = !DILocation(line: 2, column: 29, scope: !9)
!15 = !DILocation(line: 4, column: 11, scope: !9)
!16 = !DILocation(line: 4, column: 3, scope: !9)
!17 = !DILocation(line: 6, column: 5, scope: !18)
!18 = distinct !DILexicalBlock(scope: !9, file: !6, line: 4, column: 15)
!19 = !DILocation(line: 8, column: 5, scope: !18)
!20 = !DILocation(line: 10, column: 5, scope: !18)
!21 = !DILocation(line: 12, column: 5, scope: !18)
!22 = !DILocation(line: 14, column: 5, scope: !18)
!23 = !DILocation(line: 16, column: 1, scope: !9)
