; ModuleID = 'vectortest.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.14.0"

@.str = private unnamed_addr constant [5 x i8] c"%02X\00", align 1
@.str.1 = private unnamed_addr constant [2 x i8] c" \00", align 1
@.str.2 = private unnamed_addr constant [2 x i8] c"\0A\00", align 1
@main.array = private unnamed_addr constant [4 x i32] [i32 1442454, i32 2242865, i32 3676852, i32 4486525], align 16
@main.final_array = private unnamed_addr constant [4 x i32] [i32 -317271676, i32 1290222275, i32 1063726540, i32 10295], align 16

; Function Attrs: nounwind ssp uwtable
define void @printBytes(i8* nocapture readonly %byte_array, i32 %bytes) #0 !dbg !30 {
entry:
  tail call void @llvm.dbg.value(metadata i8* %byte_array, i64 0, metadata !36, metadata !59), !dbg !60
  tail call void @llvm.dbg.value(metadata i32 %bytes, i64 0, metadata !37, metadata !59), !dbg !61
  tail call void @llvm.dbg.value(metadata i32 0, i64 0, metadata !38, metadata !59), !dbg !62
  %cmp20 = icmp sgt i32 %bytes, 0, !dbg !63
  br i1 %cmp20, label %while.body, label %while.end, !dbg !64

while.body:                                       ; preds = %entry, %while.cond.backedge
  %indvars.iv = phi i64 [ %indvars.iv.next, %while.cond.backedge ], [ 0, %entry ]
  %arrayidx = getelementptr inbounds i8, i8* %byte_array, i64 %indvars.iv, !dbg !65
  %0 = load i8, i8* %arrayidx, align 1, !dbg !65, !tbaa !67
  %conv = zext i8 %0 to i32, !dbg !70
  %call = tail call i32 (i8*, ...) @printf(i8* nonnull getelementptr inbounds ([5 x i8], [5 x i8]* @.str, i64 0, i64 0), i32 %conv), !dbg !71
  %indvars.iv.next = add nuw nsw i64 %indvars.iv, 1, !dbg !64
  %rem16 = and i64 %indvars.iv.next, 1, !dbg !72
  %cmp1 = icmp eq i64 %rem16, 0, !dbg !72
  br i1 %cmp1, label %if.then, label %if.end, !dbg !74

if.then:                                          ; preds = %while.body
  %putchar19 = tail call i32 @putchar(i32 32) #4, !dbg !75
  br label %if.end, !dbg !75

if.end:                                           ; preds = %if.then, %while.body
  %rem417 = and i64 %indvars.iv.next, 3, !dbg !76
  %cmp5 = icmp eq i64 %rem417, 0, !dbg !76
  br i1 %cmp5, label %if.then7, label %while.cond.backedge, !dbg !78

if.then7:                                         ; preds = %if.end
  %putchar18 = tail call i32 @putchar(i32 10) #4, !dbg !79
  br label %while.cond.backedge, !dbg !79

while.cond.backedge:                              ; preds = %if.then7, %if.end
  %lftr.wideiv = trunc i64 %indvars.iv.next to i32, !dbg !64
  %exitcond = icmp eq i32 %lftr.wideiv, %bytes, !dbg !64
  br i1 %exitcond, label %while.end, label %while.body, !dbg !64

while.end:                                        ; preds = %while.cond.backedge, %entry
  %putchar = tail call i32 @putchar(i32 10) #4, !dbg !80
  ret void, !dbg !81
}

; Function Attrs: nounwind readnone
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: nounwind
declare i32 @printf(i8* nocapture readonly, ...) #2

; Function Attrs: nounwind ssp uwtable
define i32 @main(i32 %argc, i8** nocapture readnone %argv) #0 !dbg !39 {
entry:
  tail call void @llvm.dbg.value(metadata i32 %argc, i64 0, metadata !44, metadata !59), !dbg !82
  tail call void @llvm.dbg.value(metadata i8** %argv, i64 0, metadata !45, metadata !59), !dbg !83
  %call = tail call i8* @malloc(i64 128), !dbg !84
  %0 = bitcast i8* %call to <2 x i64>*, !dbg !84
  tail call void @llvm.dbg.value(metadata <2 x i64>* %0, i64 0, metadata !48, metadata !59), !dbg !85
  tail call void @llvm.dbg.declare(metadata [4 x i32]* @main.array, metadata !49, metadata !59), !dbg !86
  tail call void @llvm.dbg.value(metadata <2 x i64> <i64 9633031825785494, i64 19269478151363252>, i64 0, metadata !46, metadata !59), !dbg !87
  tail call void @llvm.dbg.value(metadata <2 x i64> <i64 5541462479673414020, i64 44217752038860>, i64 0, metadata !47, metadata !59), !dbg !88
  tail call void @llvm.x86.sse2.storeu.dq(i8* %call, <16 x i8> <i8 -106, i8 2, i8 22, i8 0, i8 49, i8 57, i8 34, i8 0, i8 -76, i8 26, i8 56, i8 0, i8 125, i8 117, i8 68, i8 0>) #4, !dbg !89
  %1 = load <2 x i64>, <2 x i64>* %0, align 1, !dbg !90, !tbaa !67
  tail call void @llvm.dbg.value(metadata <2 x i64> %1, i64 0, metadata !46, metadata !59), !dbg !87
  %add5 = mul <2 x i64> %1, <i64 3, i64 3>, !dbg !91
  store <2 x i64> %add5, <2 x i64>* %0, align 16, !dbg !92, !tbaa !67
  %2 = tail call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %1, <2 x i64> %add5, i8 0), !dbg !93
  tail call void @llvm.dbg.value(metadata <2 x i64> %2, i64 0, metadata !46, metadata !59), !dbg !87
  %3 = tail call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %2, <2 x i64> %add5, i8 1), !dbg !94
  tail call void @llvm.dbg.value(metadata <2 x i64> %3, i64 0, metadata !46, metadata !59), !dbg !87
  %4 = tail call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %3, <2 x i64> %add5, i8 16), !dbg !95
  tail call void @llvm.dbg.value(metadata <2 x i64> %4, i64 0, metadata !46, metadata !59), !dbg !87
  %5 = tail call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %4, <2 x i64> %add5, i8 17), !dbg !96
  tail call void @llvm.dbg.value(metadata <2 x i64> %5, i64 0, metadata !46, metadata !59), !dbg !87
  %vecext = extractelement <2 x i64> %5, i32 0, !dbg !97
  %vecext7 = extractelement <2 x i64> %5, i32 1, !dbg !98
  %phitmp = icmp ne i64 %vecext7, 44217752038860
  %not.cmp = icmp ne i64 %vecext, 5541462479673414020, !dbg !99
  %6 = or i1 %phitmp, %not.cmp, !dbg !99
  %lnot.ext = zext i1 %6 to i32, !dbg !100
  ret i32 %lnot.ext, !dbg !101
}

; Function Attrs: nounwind
declare noalias i8* @malloc(i64) #2

; Function Attrs: nounwind readnone
declare <2 x i64> @llvm.x86.pclmulqdq(<2 x i64>, <2 x i64>, i8) #1

; Function Attrs: argmemonly nounwind
declare void @llvm.x86.sse2.storeu.dq(i8*, <16 x i8>) #3

; Function Attrs: nounwind readnone
declare void @llvm.dbg.value(metadata, i64, metadata, metadata) #1

declare i32 @putchar(i32)

attributes #0 = { nounwind ssp uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="core2" "target-features"="+cx16,+fxsr,+mmx,+pclmul,+sse,+sse2,+sse3,+ssse3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone }
attributes #2 = { nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="core2" "target-features"="+cx16,+fxsr,+mmx,+pclmul,+sse,+sse2,+sse3,+ssse3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { argmemonly nounwind }
attributes #4 = { nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!55, !56, !57}
!llvm.ident = !{!58}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 3.8.1 (tags/RELEASE_381/final)", isOptimized: true, runtimeVersion: 0, emissionKind: 1, enums: !2, retainedTypes: !3, subprograms: !29)
!1 = !DIFile(filename: "vectortest.c", directory: "/Users/rdockins/code/saw-script/intTests/test0030_vectors")
!2 = !{}
!3 = !{!4, !5, !6, !12, !13, !18, !24, !28}
!4 = !DIBasicType(name: "unsigned int", size: 32, align: 32, encoding: DW_ATE_unsigned)
!5 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !6, size: 64, align: 64)
!6 = !DIDerivedType(tag: DW_TAG_typedef, name: "__m128i", file: !7, line: 30, baseType: !8)
!7 = !DIFile(filename: "/usr/local/Cellar/llvm@3.8/3.8.1/lib/llvm-3.8/bin/../lib/clang/3.8.1/include/emmintrin.h", directory: "/Users/rdockins/code/saw-script/intTests/test0030_vectors")
!8 = !DICompositeType(tag: DW_TAG_array_type, baseType: !9, size: 128, align: 128, flags: DIFlagVector, elements: !10)
!9 = !DIBasicType(name: "long long int", size: 64, align: 64, encoding: DW_ATE_signed)
!10 = !{!11}
!11 = !DISubrange(count: 2)
!12 = !DIDerivedType(tag: DW_TAG_typedef, name: "__v2di", file: !7, line: 34, baseType: !8)
!13 = !DIDerivedType(tag: DW_TAG_typedef, name: "__v16qi", file: !7, line: 36, baseType: !14)
!14 = !DICompositeType(tag: DW_TAG_array_type, baseType: !15, size: 128, align: 128, flags: DIFlagVector, elements: !16)
!15 = !DIBasicType(name: "char", size: 8, align: 8, encoding: DW_ATE_signed_char)
!16 = !{!17}
!17 = !DISubrange(count: 16)
!18 = !DIDerivedType(tag: DW_TAG_typedef, name: "__v4si", file: !19, line: 29, baseType: !20)
!19 = !DIFile(filename: "/usr/local/Cellar/llvm@3.8/3.8.1/lib/llvm-3.8/bin/../lib/clang/3.8.1/include/xmmintrin.h", directory: "/Users/rdockins/code/saw-script/intTests/test0030_vectors")
!20 = !DICompositeType(tag: DW_TAG_array_type, baseType: !21, size: 128, align: 128, flags: DIFlagVector, elements: !22)
!21 = !DIBasicType(name: "int", size: 32, align: 32, encoding: DW_ATE_signed)
!22 = !{!23}
!23 = !DISubrange(count: 4)
!24 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !25, size: 64, align: 64)
!25 = !DICompositeType(tag: DW_TAG_structure_type, name: "__loadu_si128", file: !7, line: 1114, size: 128, align: 8, elements: !26)
!26 = !{!27}
!27 = !DIDerivedType(tag: DW_TAG_member, name: "__v", scope: !25, file: !7, line: 1115, baseType: !6, size: 128, align: 128)
!28 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !15, size: 64, align: 64)
!29 = !{!30, !39}
!30 = distinct !DISubprogram(name: "printBytes", scope: !1, file: !1, line: 7, type: !31, isLocal: false, isDefinition: true, scopeLine: 7, flags: DIFlagPrototyped, isOptimized: true, variables: !35)
!31 = !DISubroutineType(types: !32)
!32 = !{null, !33, !21}
!33 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !34, size: 64, align: 64)
!34 = !DIBasicType(name: "unsigned char", size: 8, align: 8, encoding: DW_ATE_unsigned_char)
!35 = !{!36, !37, !38}
!36 = !DILocalVariable(name: "byte_array", arg: 1, scope: !30, file: !1, line: 7, type: !33)
!37 = !DILocalVariable(name: "bytes", arg: 2, scope: !30, file: !1, line: 7, type: !21)
!38 = !DILocalVariable(name: "i", scope: !30, file: !1, line: 8, type: !21)
!39 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 19, type: !40, isLocal: false, isDefinition: true, scopeLine: 20, flags: DIFlagPrototyped, isOptimized: true, variables: !43)
!40 = !DISubroutineType(types: !41)
!41 = !{!21, !21, !42}
!42 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !28, size: 64, align: 64)
!43 = !{!44, !45, !46, !47, !48, !49, !53, !54}
!44 = !DILocalVariable(name: "argc", arg: 1, scope: !39, file: !1, line: 19, type: !21)
!45 = !DILocalVariable(name: "argv", arg: 2, scope: !39, file: !1, line: 19, type: !42)
!46 = !DILocalVariable(name: "vector", scope: !39, file: !1, line: 21, type: !6)
!47 = !DILocalVariable(name: "final_vector", scope: !39, file: !1, line: 22, type: !6)
!48 = !DILocalVariable(name: "vector2", scope: !39, file: !1, line: 23, type: !5)
!49 = !DILocalVariable(name: "array", scope: !39, file: !1, line: 24, type: !50)
!50 = !DICompositeType(tag: DW_TAG_array_type, baseType: !51, size: 128, align: 32, elements: !22)
!51 = !DIDerivedType(tag: DW_TAG_typedef, name: "int32_t", file: !52, line: 30, baseType: !21)
!52 = !DIFile(filename: "/usr/include/sys/_types/_int32_t.h", directory: "/Users/rdockins/code/saw-script/intTests/test0030_vectors")
!53 = !DILocalVariable(name: "final_array", scope: !39, file: !1, line: 25, type: !50)
!54 = !DILocalVariable(name: "result", scope: !39, file: !1, line: 48, type: !21)
!55 = !{i32 2, !"Dwarf Version", i32 2}
!56 = !{i32 2, !"Debug Info Version", i32 3}
!57 = !{i32 1, !"PIC Level", i32 2}
!58 = !{!"clang version 3.8.1 (tags/RELEASE_381/final)"}
!59 = !DIExpression()
!60 = !DILocation(line: 7, column: 33, scope: !30)
!61 = !DILocation(line: 7, column: 49, scope: !30)
!62 = !DILocation(line: 8, column: 7, scope: !30)
!63 = !DILocation(line: 9, column: 12, scope: !30)
!64 = !DILocation(line: 9, column: 3, scope: !30)
!65 = !DILocation(line: 11, column: 31, scope: !66)
!66 = distinct !DILexicalBlock(scope: !30, file: !1, line: 10, column: 3)
!67 = !{!68, !68, i64 0}
!68 = !{!"omnipotent char", !69, i64 0}
!69 = !{!"Simple C/C++ TBAA"}
!70 = !DILocation(line: 11, column: 21, scope: !66)
!71 = !DILocation(line: 11, column: 7, scope: !66)
!72 = !DILocation(line: 13, column: 14, scope: !73)
!73 = distinct !DILexicalBlock(scope: !66, file: !1, line: 13, column: 10)
!74 = !DILocation(line: 13, column: 10, scope: !66)
!75 = !DILocation(line: 13, column: 20, scope: !73)
!76 = !DILocation(line: 14, column: 13, scope: !77)
!77 = distinct !DILexicalBlock(scope: !66, file: !1, line: 14, column: 10)
!78 = !DILocation(line: 14, column: 10, scope: !66)
!79 = !DILocation(line: 14, column: 19, scope: !77)
!80 = !DILocation(line: 16, column: 3, scope: !30)
!81 = !DILocation(line: 17, column: 1, scope: !30)
!82 = !DILocation(line: 19, column: 14, scope: !39)
!83 = !DILocation(line: 19, column: 26, scope: !39)
!84 = !DILocation(line: 23, column: 22, scope: !39)
!85 = !DILocation(line: 23, column: 12, scope: !39)
!86 = !DILocation(line: 24, column: 11, scope: !39)
!87 = !DILocation(line: 21, column: 11, scope: !39)
!88 = !DILocation(line: 22, column: 11, scope: !39)
!89 = !DILocation(line: 33, column: 3, scope: !39)
!90 = !DILocation(line: 34, column: 12, scope: !39)
!91 = !DILocation(line: 40, column: 30, scope: !39)
!92 = !DILocation(line: 40, column: 12, scope: !39)
!93 = !DILocation(line: 43, column: 12, scope: !39)
!94 = !DILocation(line: 44, column: 12, scope: !39)
!95 = !DILocation(line: 45, column: 12, scope: !39)
!96 = !DILocation(line: 46, column: 12, scope: !39)
!97 = !DILocation(line: 48, column: 17, scope: !39)
!98 = !DILocation(line: 48, column: 51, scope: !39)
!99 = !DILocation(line: 48, column: 47, scope: !39)
!100 = !DILocation(line: 64, column: 10, scope: !39)
!101 = !DILocation(line: 64, column: 3, scope: !39)
