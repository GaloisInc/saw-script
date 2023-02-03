; ModuleID = 'test.c'
source_filename = "test.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@x = dso_local local_unnamed_addr global i32 0, align 4, !dbg !0

; Function Attrs: nofree norecurse nounwind uwtable
define dso_local i32 @f(i32 %0) local_unnamed_addr #0 !dbg !12 {
  call void @llvm.dbg.value(metadata i32 %0, metadata !16, metadata !DIExpression()), !dbg !17
  %2 = load i32, i32* @x, align 4, !dbg !18, !tbaa !19
  %3 = add i32 %2, 1, !dbg !23
  store i32 %3, i32* @x, align 4, !dbg !24, !tbaa !19
  %4 = add i32 %3, %0, !dbg !25
  ret i32 %4, !dbg !26
}

; Function Attrs: nofree norecurse nounwind uwtable
define dso_local i32 @g(i32 %0) local_unnamed_addr #0 !dbg !27 {
  call void @llvm.dbg.value(metadata i32 %0, metadata !29, metadata !DIExpression()), !dbg !30
  %2 = load i32, i32* @x, align 4, !dbg !31, !tbaa !19
  %3 = add i32 %2, 2, !dbg !32
  store i32 %3, i32* @x, align 4, !dbg !33, !tbaa !19
  %4 = add i32 %3, %0, !dbg !34
  ret i32 %4, !dbg !35
}

; Function Attrs: nofree norecurse nounwind uwtable
define dso_local i32 @h(i32 %0) local_unnamed_addr #0 !dbg !36 {
  call void @llvm.dbg.value(metadata i32 %0, metadata !38, metadata !DIExpression()), !dbg !39
  %2 = call i32 @f(i32 %0), !dbg !40
  %3 = call i32 @g(i32 %2), !dbg !41
  ret i32 %3, !dbg !42
}

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.value(metadata, metadata, metadata) #1

attributes #0 = { nofree norecurse nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable willreturn }

!llvm.dbg.cu = !{!2}
!llvm.module.flags = !{!7, !8, !9}
!llvm.ident = !{!10}
!llvm.commandline = !{!11}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(name: "x", scope: !2, file: !3, line: 1, type: !6, isLocal: false, isDefinition: true)
!2 = distinct !DICompileUnit(language: DW_LANG_C99, file: !3, producer: "clang version 10.0.0-4ubuntu1 ", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !4, globals: !5, splitDebugInlining: false, nameTableKind: None)
!3 = !DIFile(filename: "test.c", directory: "/home/rscott/Documents/Hacking/Haskell/saw-script/intTests/test0036_global")
!4 = !{}
!5 = !{!0}
!6 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!7 = !{i32 7, !"Dwarf Version", i32 4}
!8 = !{i32 2, !"Debug Info Version", i32 3}
!9 = !{i32 1, !"wchar_size", i32 4}
!10 = !{!"clang version 10.0.0-4ubuntu1 "}
!11 = !{!"/usr/lib/llvm-10/bin/clang -g -emit-llvm -frecord-command-line -O1 -S test.c -o test-O1.ll"}
!12 = distinct !DISubprogram(name: "f", scope: !3, file: !3, line: 3, type: !13, scopeLine: 3, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !15)
!13 = !DISubroutineType(types: !14)
!14 = !{!6, !6}
!15 = !{!16}
!16 = !DILocalVariable(name: "y", arg: 1, scope: !12, file: !3, line: 3, type: !6)
!17 = !DILocation(line: 0, scope: !12)
!18 = !DILocation(line: 4, column: 7, scope: !12)
!19 = !{!20, !20, i64 0}
!20 = !{!"int", !21, i64 0}
!21 = !{!"omnipotent char", !22, i64 0}
!22 = !{!"Simple C/C++ TBAA"}
!23 = !DILocation(line: 4, column: 9, scope: !12)
!24 = !DILocation(line: 4, column: 5, scope: !12)
!25 = !DILocation(line: 5, column: 12, scope: !12)
!26 = !DILocation(line: 5, column: 3, scope: !12)
!27 = distinct !DISubprogram(name: "g", scope: !3, file: !3, line: 8, type: !13, scopeLine: 8, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !28)
!28 = !{!29}
!29 = !DILocalVariable(name: "z", arg: 1, scope: !27, file: !3, line: 8, type: !6)
!30 = !DILocation(line: 0, scope: !27)
!31 = !DILocation(line: 9, column: 7, scope: !27)
!32 = !DILocation(line: 9, column: 9, scope: !27)
!33 = !DILocation(line: 9, column: 5, scope: !27)
!34 = !DILocation(line: 10, column: 12, scope: !27)
!35 = !DILocation(line: 10, column: 3, scope: !27)
!36 = distinct !DISubprogram(name: "h", scope: !3, file: !3, line: 13, type: !13, scopeLine: 13, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !37)
!37 = !{!38}
!38 = !DILocalVariable(name: "w", arg: 1, scope: !36, file: !3, line: 13, type: !6)
!39 = !DILocation(line: 0, scope: !36)
!40 = !DILocation(line: 14, column: 12, scope: !36)
!41 = !DILocation(line: 14, column: 10, scope: !36)
!42 = !DILocation(line: 14, column: 3, scope: !36)
