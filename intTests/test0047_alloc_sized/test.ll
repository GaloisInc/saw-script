; ModuleID = 'test.c'
source_filename = "test.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.B = type { i32 }
%struct.A = type { i32 }

; Function Attrs: nounwind readnone sspstrong uwtable
define %struct.B* @cast_as_b(%struct.A* readnone) local_unnamed_addr #0 !dbg !26 {
  tail call void @llvm.dbg.value(metadata %struct.A* %0, i64 0, metadata !31, metadata !34), !dbg !35
  tail call void @llvm.dbg.value(metadata %struct.A* %0, i64 0, metadata !32, metadata !34), !dbg !36
  tail call void @llvm.dbg.value(metadata %struct.A* %0, i64 0, metadata !33, metadata !34), !dbg !37
  %2 = getelementptr inbounds %struct.A, %struct.A* %0, i64 1, i32 0, !dbg !38
  %3 = bitcast i32* %2 to %struct.B*, !dbg !39
  ret %struct.B* %3, !dbg !40
}

; Function Attrs: nounwind sspstrong uwtable
define void @set(%struct.A*) local_unnamed_addr #1 !dbg !41 {
  tail call void @llvm.dbg.value(metadata %struct.A* %0, i64 0, metadata !45, metadata !34), !dbg !47
  %2 = getelementptr inbounds %struct.A, %struct.A* %0, i64 0, i32 0, !dbg !48
  store i32 10, i32* %2, align 4, !dbg !49, !tbaa !50
  %3 = tail call %struct.B* @cast_as_b(%struct.A* %0), !dbg !55
  tail call void @llvm.dbg.value(metadata %struct.B* %3, i64 0, metadata !46, metadata !34), !dbg !56
  %4 = getelementptr inbounds %struct.B, %struct.B* %3, i64 0, i32 0, !dbg !57
  store i32 42, i32* %4, align 4, !dbg !58, !tbaa !59
  ret void, !dbg !61
}

; Function Attrs: nounwind sspstrong uwtable
define i32 @main() local_unnamed_addr #1 !dbg !62 {
  tail call void @llvm.dbg.value(metadata i64 8, i64 0, metadata !66, metadata !34), !dbg !72
  %1 = tail call noalias i8* @malloc(i64 8) #4, !dbg !73
  %2 = bitcast i8* %1 to %struct.A*, !dbg !73
  tail call void @llvm.dbg.value(metadata %struct.A* %2, i64 0, metadata !70, metadata !34), !dbg !74
  %3 = bitcast i8* %1 to i64*, !dbg !75
  store i64 0, i64* %3, align 4, !dbg !75
  tail call void @set(%struct.A* %2), !dbg !76
  %4 = tail call %struct.B* @cast_as_b(%struct.A* %2), !dbg !77
  tail call void @llvm.dbg.value(metadata %struct.B* %4, i64 0, metadata !71, metadata !34), !dbg !78
  %5 = getelementptr inbounds %struct.B, %struct.B* %4, i64 0, i32 0, !dbg !79
  %6 = load i32, i32* %5, align 4, !dbg !79, !tbaa !59
  ret i32 %6, !dbg !80
}

; Function Attrs: nounwind
declare noalias i8* @malloc(i64) local_unnamed_addr #2

; Function Attrs: nounwind readnone speculatable
declare void @llvm.dbg.value(metadata, i64, metadata, metadata) #3

attributes #0 = { nounwind readnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind readnone speculatable }
attributes #4 = { nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!21, !22, !23, !24}
!llvm.ident = !{!25}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 5.0.2 (tags/RELEASE_502/final)", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, retainedTypes: !3)
!1 = !DIFile(filename: "test.c", directory: "/home/siddharthist/code/saw-script/intTests/test0047_alloc_sized")
!2 = !{}
!3 = !{!4, !5, !16}
!4 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64)
!5 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !6, size: 64)
!6 = !DIDerivedType(tag: DW_TAG_typedef, name: "C_t", file: !1, line: 15, baseType: !7)
!7 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "C", file: !1, line: 12, size: 64, elements: !8)
!8 = !{!9, !15}
!9 = !DIDerivedType(tag: DW_TAG_member, name: "a", scope: !7, file: !1, line: 13, baseType: !10, size: 32)
!10 = !DIDerivedType(tag: DW_TAG_typedef, name: "A_t", file: !1, line: 6, baseType: !11)
!11 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "A", file: !1, line: 4, size: 32, elements: !12)
!12 = !{!13}
!13 = !DIDerivedType(tag: DW_TAG_member, name: "x", scope: !11, file: !1, line: 5, baseType: !14, size: 32)
!14 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!15 = !DIDerivedType(tag: DW_TAG_member, name: "z", scope: !7, file: !1, line: 14, baseType: !14, size: 32, offset: 32)
!16 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !17, size: 64)
!17 = !DIDerivedType(tag: DW_TAG_typedef, name: "B_t", file: !1, line: 10, baseType: !18)
!18 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "B", file: !1, line: 8, size: 32, elements: !19)
!19 = !{!20}
!20 = !DIDerivedType(tag: DW_TAG_member, name: "y", scope: !18, file: !1, line: 9, baseType: !14, size: 32)
!21 = !{i32 2, !"Dwarf Version", i32 4}
!22 = !{i32 2, !"Debug Info Version", i32 3}
!23 = !{i32 1, !"wchar_size", i32 4}
!24 = !{i32 7, !"PIC Level", i32 2}
!25 = !{!"clang version 5.0.2 (tags/RELEASE_502/final)"}
!26 = distinct !DISubprogram(name: "cast_as_b", scope: !1, file: !1, line: 17, type: !27, isLocal: false, isDefinition: true, scopeLine: 17, flags: DIFlagPrototyped, isOptimized: true, unit: !0, variables: !30)
!27 = !DISubroutineType(types: !28)
!28 = !{!16, !29}
!29 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !10, size: 64)
!30 = !{!31, !32, !33}
!31 = !DILocalVariable(name: "both", arg: 1, scope: !26, file: !1, line: 17, type: !29)
!32 = !DILocalVariable(name: "v", scope: !26, file: !1, line: 18, type: !4)
!33 = !DILocalVariable(name: "c", scope: !26, file: !1, line: 19, type: !5)
!34 = !DIExpression()
!35 = !DILocation(line: 17, column: 21, scope: !26)
!36 = !DILocation(line: 18, column: 9, scope: !26)
!37 = !DILocation(line: 19, column: 8, scope: !26)
!38 = !DILocation(line: 20, column: 30, scope: !26)
!39 = !DILocation(line: 20, column: 10, scope: !26)
!40 = !DILocation(line: 20, column: 3, scope: !26)
!41 = distinct !DISubprogram(name: "set", scope: !1, file: !1, line: 23, type: !42, isLocal: false, isDefinition: true, scopeLine: 23, flags: DIFlagPrototyped, isOptimized: true, unit: !0, variables: !44)
!42 = !DISubroutineType(types: !43)
!43 = !{null, !29}
!44 = !{!45, !46}
!45 = !DILocalVariable(name: "both", arg: 1, scope: !41, file: !1, line: 23, type: !29)
!46 = !DILocalVariable(name: "b", scope: !41, file: !1, line: 25, type: !16)
!47 = !DILocation(line: 23, column: 15, scope: !41)
!48 = !DILocation(line: 24, column: 9, scope: !41)
!49 = !DILocation(line: 24, column: 11, scope: !41)
!50 = !{!51, !52, i64 0}
!51 = !{!"A", !52, i64 0}
!52 = !{!"int", !53, i64 0}
!53 = !{!"omnipotent char", !54, i64 0}
!54 = !{!"Simple C/C++ TBAA"}
!55 = !DILocation(line: 25, column: 12, scope: !41)
!56 = !DILocation(line: 25, column: 8, scope: !41)
!57 = !DILocation(line: 26, column: 6, scope: !41)
!58 = !DILocation(line: 26, column: 8, scope: !41)
!59 = !{!60, !52, i64 0}
!60 = !{!"B", !52, i64 0}
!61 = !DILocation(line: 27, column: 1, scope: !41)
!62 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 29, type: !63, isLocal: false, isDefinition: true, scopeLine: 29, isOptimized: true, unit: !0, variables: !65)
!63 = !DISubroutineType(types: !64)
!64 = !{!14}
!65 = !{!66, !70, !71}
!66 = !DILocalVariable(name: "size_of_both", scope: !62, file: !1, line: 30, type: !67)
!67 = !DIDerivedType(tag: DW_TAG_typedef, name: "size_t", file: !68, line: 62, baseType: !69)
!68 = !DIFile(filename: "/nix/store/ah672czwlnfjxav912rv29ry62c3n9qv-clang-wrapper-5.0.2/resource-root/include/stddef.h", directory: "/home/siddharthist/code/saw-script/intTests/test0047_alloc_sized")
!69 = !DIBasicType(name: "long unsigned int", size: 64, encoding: DW_ATE_unsigned)
!70 = !DILocalVariable(name: "both", scope: !62, file: !1, line: 31, type: !29)
!71 = !DILocalVariable(name: "b", scope: !62, file: !1, line: 34, type: !16)
!72 = !DILocation(line: 30, column: 10, scope: !62)
!73 = !DILocation(line: 31, column: 15, scope: !62)
!74 = !DILocation(line: 31, column: 8, scope: !62)
!75 = !DILocation(line: 32, column: 3, scope: !62)
!76 = !DILocation(line: 33, column: 3, scope: !62)
!77 = !DILocation(line: 34, column: 12, scope: !62)
!78 = !DILocation(line: 34, column: 8, scope: !62)
!79 = !DILocation(line: 35, column: 13, scope: !62)
!80 = !DILocation(line: 35, column: 3, scope: !62)
