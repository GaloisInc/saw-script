; ModuleID = 'test.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.13.0"

%struct.BI = type { [2 x [4 x i32]] }

@.str = private unnamed_addr constant [4 x i8] c"%u\0A\00", align 1

; Function Attrs: norecurse nounwind ssp uwtable
define void @f(%struct.BI* nocapture %w) #0 !dbg !4 {
for.cond.cleanup:
  tail call void @llvm.dbg.value(metadata %struct.BI* %w, i64 0, metadata !18, metadata !35), !dbg !36
  tail call void @llvm.dbg.value(metadata i32 0, i64 0, metadata !19, metadata !35), !dbg !37
  %w22 = bitcast %struct.BI* %w to i8*
  call void @llvm.memset.p0i8.i64(i8* %w22, i8 0, i64 32, i32 4, i1 false), !dbg !38
  ret void, !dbg !41
}

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start(i64, i8* nocapture) #1

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.end(i64, i8* nocapture) #1

; Function Attrs: nounwind ssp uwtable
define i32 @main() #2 !dbg !26 {
entry:
  %x = alloca %struct.BI, align 4
  %0 = bitcast %struct.BI* %x to i8*, !dbg !42
  call void @llvm.lifetime.start(i64 32, i8* %0) #5, !dbg !42
  %arrayidx1 = getelementptr inbounds %struct.BI, %struct.BI* %x, i64 0, i32 0, i64 1, i64 3, !dbg !43
  store i32 42, i32* %arrayidx1, align 4, !dbg !44, !tbaa !45
  tail call void @llvm.dbg.value(metadata %struct.BI* %x, i64 0, metadata !30, metadata !49), !dbg !50
  call void @f(%struct.BI* nonnull %x), !dbg !51
  %1 = load i32, i32* %arrayidx1, align 4, !dbg !52, !tbaa !45
  %call = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i64 0, i64 0), i32 %1), !dbg !53
  call void @llvm.lifetime.end(i64 32, i8* %0) #5, !dbg !54
  ret i32 0, !dbg !54
}

; Function Attrs: nounwind
declare i32 @printf(i8* nocapture readonly, ...) #3

; Function Attrs: nounwind readnone
declare void @llvm.dbg.value(metadata, i64, metadata, metadata) #4

; Function Attrs: argmemonly nounwind
declare void @llvm.memset.p0i8.i64(i8* nocapture, i8, i64, i32, i1) #1

attributes #0 = { norecurse nounwind ssp uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="core2" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+ssse3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind }
attributes #2 = { nounwind ssp uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="core2" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+ssse3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="core2" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+ssse3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind readnone }
attributes #5 = { nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!31, !32, !33}
!llvm.ident = !{!34}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 3.8.1 (tags/RELEASE_381/final)", isOptimized: true, runtimeVersion: 0, emissionKind: 1, enums: !2, subprograms: !3)
!1 = !DIFile(filename: "test.c", directory: "/Users/rdockins/code/saw-script/intTests/test0028")
!2 = !{}
!3 = !{!4, !26}
!4 = distinct !DISubprogram(name: "f", scope: !1, file: !1, line: 7, type: !5, isLocal: false, isDefinition: true, scopeLine: 7, flags: DIFlagPrototyped, isOptimized: true, variables: !17)
!5 = !DISubroutineType(types: !6)
!6 = !{null, !7}
!7 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !8, size: 64, align: 64)
!8 = !DIDerivedType(tag: DW_TAG_typedef, name: "BI_t", file: !1, line: 5, baseType: !9)
!9 = !DICompositeType(tag: DW_TAG_structure_type, name: "BI", file: !1, line: 3, size: 256, align: 32, elements: !10)
!10 = !{!11}
!11 = !DIDerivedType(tag: DW_TAG_member, name: "i", scope: !9, file: !1, line: 4, baseType: !12, size: 256, align: 32)
!12 = !DICompositeType(tag: DW_TAG_array_type, baseType: !13, size: 256, align: 32, elements: !14)
!13 = !DIBasicType(name: "unsigned int", size: 32, align: 32, encoding: DW_ATE_unsigned)
!14 = !{!15, !16}
!15 = !DISubrange(count: 2)
!16 = !DISubrange(count: 4)
!17 = !{!18, !19, !22}
!18 = !DILocalVariable(name: "w", arg: 1, scope: !4, file: !1, line: 7, type: !7)
!19 = !DILocalVariable(name: "j", scope: !20, file: !1, line: 8, type: !21)
!20 = distinct !DILexicalBlock(scope: !4, file: !1, line: 8, column: 3)
!21 = !DIBasicType(name: "int", size: 32, align: 32, encoding: DW_ATE_signed)
!22 = !DILocalVariable(name: "k", scope: !23, file: !1, line: 9, type: !21)
!23 = distinct !DILexicalBlock(scope: !24, file: !1, line: 9, column: 5)
!24 = distinct !DILexicalBlock(scope: !25, file: !1, line: 8, column: 27)
!25 = distinct !DILexicalBlock(scope: !20, file: !1, line: 8, column: 3)
!26 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 15, type: !27, isLocal: false, isDefinition: true, scopeLine: 15, isOptimized: true, variables: !29)
!27 = !DISubroutineType(types: !28)
!28 = !{!21}
!29 = !{!30}
!30 = !DILocalVariable(name: "x", scope: !26, file: !1, line: 16, type: !8)
!31 = !{i32 2, !"Dwarf Version", i32 2}
!32 = !{i32 2, !"Debug Info Version", i32 3}
!33 = !{i32 1, !"PIC Level", i32 2}
!34 = !{!"clang version 3.8.1 (tags/RELEASE_381/final)"}
!35 = !DIExpression()
!36 = !DILocation(line: 7, column: 14, scope: !4)
!37 = !DILocation(line: 8, column: 12, scope: !20)
!38 = !DILocation(line: 10, column: 20, scope: !39)
!39 = distinct !DILexicalBlock(scope: !40, file: !1, line: 9, column: 29)
!40 = distinct !DILexicalBlock(scope: !23, file: !1, line: 9, column: 5)
!41 = !DILocation(line: 13, column: 1, scope: !4)
!42 = !DILocation(line: 16, column: 3, scope: !26)
!43 = !DILocation(line: 17, column: 3, scope: !26)
!44 = !DILocation(line: 17, column: 13, scope: !26)
!45 = !{!46, !46, i64 0}
!46 = !{!"int", !47, i64 0}
!47 = !{!"omnipotent char", !48, i64 0}
!48 = !{!"Simple C/C++ TBAA"}
!49 = !DIExpression(DW_OP_deref)
!50 = !DILocation(line: 16, column: 8, scope: !26)
!51 = !DILocation(line: 18, column: 3, scope: !26)
!52 = !DILocation(line: 19, column: 19, scope: !26)
!53 = !DILocation(line: 19, column: 3, scope: !26)
!54 = !DILocation(line: 20, column: 1, scope: !26)
