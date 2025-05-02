; ModuleID = 'poly.bc'
source_filename = "poly.c"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.16.0"

@.ghosts = private unnamed_addr constant [42 x i8] c"frm:llvmframe 64,a:llvmptr 64,b:llvmptr 64", align 1
@.spec = private unnamed_addr constant [90 x i8] c"arg0:eq(top1),arg1:eq(top0),top1:true,top0:ptr((R,0) |-> eq(arg0)),frm:llvmframe [b:8,a:8]", align 1
define void @heapster.require(...) { ret void }
; Function Attrs: noinline nounwind optnone ssp uwtable

define i64 @foo(i64*, i64) #0 !dbg !8 {
  %3 = alloca i64*, align 8, !heapster !100
  %4 = alloca i64, align 4
  store i64* %0, i64** %3, align 8
  call void @llvm.dbg.declare(metadata i64** %3, metadata !13, metadata !DIExpression()), !dbg !14
  store i64 %1, i64* %4, align 4
  call void @llvm.dbg.declare(metadata i64* %4, metadata !15, metadata !DIExpression()), !dbg !16
  %5 = load i64, i64* %4, align 4, !dbg !17
  %6 = icmp sgt i64 %5, 0, !dbg !19
  br i1 %6, label %7, label %10, !dbg !20

7:                                                ; preds = %2
  %8 = load i64, i64* %4, align 4, !dbg !21
  %9 = load i64*, i64** %3, align 8, !dbg !23
  store i64 %8, i64* %9, align 4, !dbg !24
  br label %13, !dbg !25

10:                                               ; preds = %2
  %11 = load i64, i64* %4, align 4, !dbg !26
  %12 = load i64*, i64** %3, align 8, !dbg !28
  store i64 %11, i64* %12, align 4, !dbg !29
  br label %13

13:                                               ; preds = %10, %7
  call void (...) @heapster.require(
    i8* getelementptr inbounds ([42 x i8], [42 x i8]* @.ghosts, i64 0, i64 0), 
    i8* getelementptr inbounds ([90 x i8], [90 x i8]* @.spec, i64 0, i64 0), 
    i64 %1,
    i64* %0 
  )

  ret i64 0, !dbg !30
}

; Function Attrs: nounwind readnone speculatable
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5, !6}
!llvm.ident = !{!7}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 9.0.1 ", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, nameTableKind: GNU)
!1 = !DIFile(filename: "poly.c", directory: "/Users/abakst/prj/saw-script/heapster-saw/examples/bc-annot")
!2 = !{}
!3 = !{i64 2, !"Dwarf Version", i64 4}
!4 = !{i64 2, !"Debug Info Version", i64 3}
!5 = !{i64 1, !"wchar_size", i64 4}
!6 = !{i64 7, !"PIC Level", i64 2}
!7 = !{!"clang version 9.0.1 "}
!8 = distinct !DISubprogram(name: "foo", scope: !1, file: !1, line: 5, type: !9, scopeLine: 5, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!9 = !DISubroutineType(types: !10)
!10 = !{!11, !12, !11}
!11 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!12 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !11, size: 64)
!13 = !DILocalVariable(name: "a", arg: 1, scope: !8, file: !1, line: 5, type: !12)
!14 = !DILocation(line: 5, column: 14, scope: !8)
!15 = !DILocalVariable(name: "b", arg: 2, scope: !8, file: !1, line: 5, type: !11)
!16 = !DILocation(line: 5, column: 21, scope: !8)
!17 = !DILocation(line: 7, column: 7, scope: !18)
!18 = distinct !DILexicalBlock(scope: !8, file: !1, line: 7, column: 7)
!19 = !DILocation(line: 7, column: 9, scope: !18)
!20 = !DILocation(line: 7, column: 7, scope: !8)
!21 = !DILocation(line: 8, column: 10, scope: !22)
!22 = distinct !DILexicalBlock(scope: !18, file: !1, line: 7, column: 14)
!23 = !DILocation(line: 8, column: 6, scope: !22)
!24 = !DILocation(line: 8, column: 8, scope: !22)
!25 = !DILocation(line: 9, column: 3, scope: !22)
!26 = !DILocation(line: 10, column: 10, scope: !27)
!27 = distinct !DILexicalBlock(scope: !18, file: !1, line: 9, column: 10)
!28 = !DILocation(line: 10, column: 6, scope: !27)
!29 = !DILocation(line: 10, column: 8, scope: !27)
!30 = !DILocation(line: 13, column: 3, scope: !8)
!100 = !{}
!101 = !{!"some spec...", !100}
