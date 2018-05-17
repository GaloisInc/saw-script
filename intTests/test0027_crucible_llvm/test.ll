; ModuleID = 'test.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.13.0"

@.str = private unnamed_addr constant [14 x i8] c"%u + %u = %u\0A\00", align 1
@.str.1 = private unnamed_addr constant [20 x i8] c"%llu + %llu = %llu\0A\00", align 1

; Function Attrs: norecurse nounwind readnone ssp uwtable
define i32 @add_nums32(i32 %x, i32 %y) #0 !dbg !4 {
entry:
  tail call void @llvm.dbg.value(metadata i32 %x, i64 0, metadata !11, metadata !30), !dbg !31
  tail call void @llvm.dbg.value(metadata i32 %y, i64 0, metadata !12, metadata !30), !dbg !32
  %add = add i32 %y, %x, !dbg !33
  ret i32 %add, !dbg !34
}

; Function Attrs: norecurse nounwind readnone ssp uwtable
define i64 @add_nums64(i64 %x, i64 %y) #0 !dbg !13 {
entry:
  tail call void @llvm.dbg.value(metadata i64 %x, i64 0, metadata !20, metadata !30), !dbg !35
  tail call void @llvm.dbg.value(metadata i64 %y, i64 0, metadata !21, metadata !30), !dbg !36
  %add = add i64 %y, %x, !dbg !37
  ret i64 %add, !dbg !38
}

; Function Attrs: nounwind ssp uwtable
define i32 @main() #1 !dbg !22 {
entry:
  %call = tail call i32 @add_nums32(i32 12, i32 30), !dbg !39
  %call1 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str, i64 0, i64 0), i32 12, i32 30, i32 %call), !dbg !40
  %call2 = tail call i64 @add_nums64(i64 12, i64 30), !dbg !41
  %call3 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([20 x i8], [20 x i8]* @.str.1, i64 0, i64 0), i64 12, i64 30, i64 %call2), !dbg !42
  ret i32 0, !dbg !43
}

; Function Attrs: nounwind
declare i32 @printf(i8* nocapture readonly, ...) #2

; Function Attrs: nounwind readnone
declare void @llvm.dbg.value(metadata, i64, metadata, metadata) #3

attributes #0 = { norecurse nounwind readnone ssp uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="core2" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+ssse3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind ssp uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="core2" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+ssse3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="core2" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+ssse3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind readnone }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!26, !27, !28}
!llvm.ident = !{!29}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 3.8.1 (tags/RELEASE_381/final)", isOptimized: true, runtimeVersion: 0, emissionKind: 1, enums: !2, subprograms: !3)
!1 = !DIFile(filename: "test.c", directory: "/Users/rdockins/code/saw-script/intTests/test0027_crucible_llvm")
!2 = !{}
!3 = !{!4, !13, !22}
!4 = distinct !DISubprogram(name: "add_nums32", scope: !1, file: !1, line: 4, type: !5, isLocal: false, isDefinition: true, scopeLine: 4, flags: DIFlagPrototyped, isOptimized: true, variables: !10)
!5 = !DISubroutineType(types: !6)
!6 = !{!7, !7, !7}
!7 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint32_t", file: !8, line: 31, baseType: !9)
!8 = !DIFile(filename: "/usr/include/_types/_uint32_t.h", directory: "/Users/rdockins/code/saw-script/intTests/test0027_crucible_llvm")
!9 = !DIBasicType(name: "unsigned int", size: 32, align: 32, encoding: DW_ATE_unsigned)
!10 = !{!11, !12}
!11 = !DILocalVariable(name: "x", arg: 1, scope: !4, file: !1, line: 4, type: !7)
!12 = !DILocalVariable(name: "y", arg: 2, scope: !4, file: !1, line: 4, type: !7)
!13 = distinct !DISubprogram(name: "add_nums64", scope: !1, file: !1, line: 8, type: !14, isLocal: false, isDefinition: true, scopeLine: 8, flags: DIFlagPrototyped, isOptimized: true, variables: !19)
!14 = !DISubroutineType(types: !15)
!15 = !{!16, !16, !16}
!16 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint64_t", file: !17, line: 31, baseType: !18)
!17 = !DIFile(filename: "/usr/include/_types/_uint64_t.h", directory: "/Users/rdockins/code/saw-script/intTests/test0027_crucible_llvm")
!18 = !DIBasicType(name: "long long unsigned int", size: 64, align: 64, encoding: DW_ATE_unsigned)
!19 = !{!20, !21}
!20 = !DILocalVariable(name: "x", arg: 1, scope: !13, file: !1, line: 8, type: !16)
!21 = !DILocalVariable(name: "y", arg: 2, scope: !13, file: !1, line: 8, type: !16)
!22 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 12, type: !23, isLocal: false, isDefinition: true, scopeLine: 12, isOptimized: true, variables: !2)
!23 = !DISubroutineType(types: !24)
!24 = !{!25}
!25 = !DIBasicType(name: "int", size: 32, align: 32, encoding: DW_ATE_signed)
!26 = !{i32 2, !"Dwarf Version", i32 2}
!27 = !{i32 2, !"Debug Info Version", i32 3}
!28 = !{i32 1, !"PIC Level", i32 2}
!29 = !{!"clang version 3.8.1 (tags/RELEASE_381/final)"}
!30 = !DIExpression()
!31 = !DILocation(line: 4, column: 31, scope: !4)
!32 = !DILocation(line: 4, column: 43, scope: !4)
!33 = !DILocation(line: 5, column: 12, scope: !4)
!34 = !DILocation(line: 5, column: 3, scope: !4)
!35 = !DILocation(line: 8, column: 31, scope: !13)
!36 = !DILocation(line: 8, column: 43, scope: !13)
!37 = !DILocation(line: 9, column: 12, scope: !13)
!38 = !DILocation(line: 9, column: 3, scope: !13)
!39 = !DILocation(line: 13, column: 38, scope: !22)
!40 = !DILocation(line: 13, column: 3, scope: !22)
!41 = !DILocation(line: 14, column: 48, scope: !22)
!42 = !DILocation(line: 14, column: 3, scope: !22)
!43 = !DILocation(line: 15, column: 3, scope: !22)
