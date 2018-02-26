; ModuleID = 'test.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.13.0"

@.str = private unnamed_addr constant [4 x i8] c"EQ!\00", align 1
@.str.1 = private unnamed_addr constant [4 x i8] c"LT!\00", align 1
@global_string = global [6 x i8] c"asdf\0A\00", align 1

; Function Attrs: nounwind ssp uwtable
define i32 @read_after_free() #0 !dbg !8 {
entry:
  %call = tail call i8* @malloc(i64 4), !dbg !89
  %0 = bitcast i8* %call to i32*, !dbg !89
  tail call void @llvm.dbg.value(metadata i32* %0, i64 0, metadata !12, metadata !90), !dbg !91
  store volatile i32 1, i32* %0, align 4, !dbg !92, !tbaa !93
  tail call void @free(i8* %call), !dbg !97
  %1 = load volatile i32, i32* %0, align 4, !dbg !98, !tbaa !93
  ret i32 %1, !dbg !99
}

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start(i64, i8* nocapture) #1

; Function Attrs: nounwind
declare noalias i8* @malloc(i64) #2

; Function Attrs: nounwind
declare void @free(i8* nocapture) #2

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.end(i64, i8* nocapture) #1

; Function Attrs: nounwind ssp uwtable
define i32 @write_after_free() #0 !dbg !15 {
entry:
  %call = tail call i8* @malloc(i64 4), !dbg !100
  %0 = bitcast i8* %call to i32*, !dbg !100
  tail call void @llvm.dbg.value(metadata i32* %0, i64 0, metadata !17, metadata !90), !dbg !101
  store volatile i32 42, i32* %0, align 4, !dbg !102, !tbaa !93
  tail call void @free(i8* %call), !dbg !103
  store volatile i32 12, i32* %0, align 4, !dbg !104, !tbaa !93
  ret i32 1, !dbg !105
}

; Function Attrs: nounwind ssp uwtable
define i32 @double_free() #0 !dbg !18 {
entry:
  %call = tail call i8* @malloc(i64 4), !dbg !106
  %0 = bitcast i8* %call to i32*, !dbg !106
  tail call void @llvm.dbg.value(metadata i32* %0, i64 0, metadata !20, metadata !90), !dbg !107
  store volatile i32 12, i32* %0, align 4, !dbg !108, !tbaa !93
  tail call void @free(i8* %call), !dbg !109
  tail call void @free(i8* %call), !dbg !110
  ret i32 1, !dbg !111
}

; Function Attrs: norecurse nounwind readnone ssp uwtable
define i32 @test_equal(i8* readnone %x, i8* readnone %y) #3 !dbg !21 {
entry:
  tail call void @llvm.dbg.value(metadata i8* %x, i64 0, metadata !25, metadata !90), !dbg !112
  tail call void @llvm.dbg.value(metadata i8* %y, i64 0, metadata !26, metadata !90), !dbg !113
  %cmp = icmp eq i8* %x, %y, !dbg !114
  %conv = zext i1 %cmp to i32, !dbg !114
  ret i32 %conv, !dbg !115
}

; Function Attrs: norecurse nounwind readnone ssp uwtable
define i32 @test_lt(i8* readnone %x, i8* readnone %y) #3 !dbg !27 {
entry:
  tail call void @llvm.dbg.value(metadata i8* %x, i64 0, metadata !29, metadata !90), !dbg !116
  tail call void @llvm.dbg.value(metadata i8* %y, i64 0, metadata !30, metadata !90), !dbg !117
  %cmp = icmp ult i8* %x, %y, !dbg !118
  %conv = zext i1 %cmp to i32, !dbg !118
  ret i32 %conv, !dbg !119
}

; Function Attrs: nounwind ssp uwtable
define i32 @equals_after_free() #0 !dbg !31 {
entry:
  %call = tail call i8* @malloc(i64 4), !dbg !120
  %0 = bitcast i8* %call to i32*, !dbg !120
  tail call void @llvm.dbg.value(metadata i32* %0, i64 0, metadata !33, metadata !90), !dbg !121
  store volatile i32 12, i32* %0, align 4, !dbg !122, !tbaa !93
  tail call void @free(i8* %call), !dbg !123
  %call1 = tail call i32 @test_equal(i8* %call, i8* %call), !dbg !124
  %tobool = icmp eq i32 %call1, 0, !dbg !124
  br i1 %tobool, label %if.end, label %if.then, !dbg !126

if.then:                                          ; preds = %entry
  %call2 = tail call i32 @puts(i8* nonnull getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i64 0, i64 0)), !dbg !127
  br label %if.end, !dbg !129

if.end:                                           ; preds = %entry, %if.then
  ret i32 1, !dbg !130
}

; Function Attrs: nounwind
declare i32 @puts(i8* nocapture readonly) #2

; Function Attrs: nounwind ssp uwtable
define i32 @le_after_free() #0 !dbg !34 {
entry:
  %call = tail call i8* @malloc(i64 32), !dbg !131
  tail call void @llvm.dbg.value(metadata i8* %call, i64 0, metadata !36, metadata !90), !dbg !132
  %add.ptr = getelementptr inbounds i8, i8* %call, i64 5, !dbg !133
  tail call void @llvm.dbg.value(metadata i8* %add.ptr, i64 0, metadata !40, metadata !90), !dbg !134
  tail call void @free(i8* %call), !dbg !135
  %call1 = tail call i32 @test_lt(i8* %call, i8* %add.ptr), !dbg !136
  %tobool = icmp eq i32 %call1, 0, !dbg !136
  br i1 %tobool, label %if.end, label %if.then, !dbg !138

if.then:                                          ; preds = %entry
  %call2 = tail call i32 @puts(i8* nonnull getelementptr inbounds ([4 x i8], [4 x i8]* @.str.1, i64 0, i64 0)), !dbg !139
  br label %if.end, !dbg !141

if.end:                                           ; preds = %entry, %if.then
  ret i32 1, !dbg !142
}

; Function Attrs: nounwind ssp uwtable
define i32 @le_different_allocs() #0 !dbg !41 {
entry:
  %call = tail call i8* @malloc(i64 4), !dbg !143
  %0 = bitcast i8* %call to i32*, !dbg !143
  tail call void @llvm.dbg.value(metadata i32* %0, i64 0, metadata !43, metadata !90), !dbg !144
  %call1 = tail call i8* @malloc(i64 4), !dbg !145
  %1 = bitcast i8* %call1 to i32*, !dbg !145
  tail call void @llvm.dbg.value(metadata i32* %1, i64 0, metadata !44, metadata !90), !dbg !146
  store volatile i32 12, i32* %0, align 4, !dbg !147, !tbaa !93
  store volatile i32 32, i32* %1, align 4, !dbg !148, !tbaa !93
  %call2 = tail call i32 @test_lt(i8* %call, i8* %call1), !dbg !149
  %tobool = icmp eq i32 %call2, 0, !dbg !149
  br i1 %tobool, label %if.end, label %if.then, !dbg !151

if.then:                                          ; preds = %entry
  %call3 = tail call i32 @puts(i8* nonnull getelementptr inbounds ([4 x i8], [4 x i8]* @.str.1, i64 0, i64 0)), !dbg !152
  br label %if.end, !dbg !154

if.end:                                           ; preds = %entry, %if.then
  ret i32 1, !dbg !155
}

; Function Attrs: norecurse nounwind ssp uwtable
define noalias nonnull i32* @leak_pointer() #4 !dbg !45 {
entry:
  %x = alloca i32, align 4
  %0 = bitcast i32* %x to i8*, !dbg !156
  call void @llvm.lifetime.start(i64 4, i8* %0) #6, !dbg !156
  tail call void @llvm.dbg.value(metadata i32* %x, i64 0, metadata !50, metadata !90), !dbg !157
  tail call void @llvm.dbg.value(metadata i32 1, i64 0, metadata !49, metadata !90), !dbg !158
  store volatile i32 1, i32* %x, align 4, !dbg !159, !tbaa !93
  call void @llvm.lifetime.end(i64 4, i8* %0) #6, !dbg !160
  ret i32* %x, !dbg !161
}

; Function Attrs: norecurse nounwind ssp uwtable
define i32 @read_after_stack_free() #4 !dbg !51 {
entry:
  %call = tail call i32* @leak_pointer(), !dbg !162
  tail call void @llvm.dbg.value(metadata i32* %call, i64 0, metadata !53, metadata !90), !dbg !163
  %0 = load i32, i32* %call, align 4, !dbg !164, !tbaa !93
  ret i32 %0, !dbg !165
}

; Function Attrs: norecurse nounwind ssp uwtable
define i32 @write_after_stack_free() #4 !dbg !54 {
entry:
  %call = tail call i32* @leak_pointer(), !dbg !166
  tail call void @llvm.dbg.value(metadata i32* %call, i64 0, metadata !56, metadata !90), !dbg !167
  store i32 12, i32* %call, align 4, !dbg !168, !tbaa !93
  ret i32 1, !dbg !169
}

; Function Attrs: nounwind ssp uwtable
define i32 @free_after_stack_free() #0 !dbg !57 {
entry:
  %call = tail call i32* @leak_pointer(), !dbg !170
  tail call void @llvm.dbg.value(metadata i32* %call, i64 0, metadata !59, metadata !90), !dbg !171
  %0 = bitcast i32* %call to i8*, !dbg !172
  tail call void @free(i8* %0), !dbg !173
  ret i32 1, !dbg !174
}

; Function Attrs: nounwind ssp uwtable
define void @subfn(i8* nocapture %x) #0 !dbg !60 {
entry:
  tail call void @llvm.dbg.value(metadata i8* %x, i64 0, metadata !64, metadata !90), !dbg !175
  tail call void @free(i8* %x), !dbg !176
  ret void, !dbg !177
}

; Function Attrs: nounwind ssp uwtable
define i32 @free_local() #0 !dbg !65 {
entry:
  %x = alloca i32, align 4
  %0 = bitcast i32* %x to i8*, !dbg !178
  call void @llvm.lifetime.start(i64 4, i8* %0) #6, !dbg !178
  tail call void @llvm.dbg.value(metadata i32 12, i64 0, metadata !67, metadata !90), !dbg !179
  store volatile i32 12, i32* %x, align 4, !dbg !179, !tbaa !93
  call void @subfn(i8* %0), !dbg !180
  call void @llvm.lifetime.end(i64 4, i8* %0) #6, !dbg !181
  ret i32 1, !dbg !182
}

; Function Attrs: nounwind ssp uwtable
define i32 @equals_after_stack_free() #0 !dbg !68 {
entry:
  %call = tail call i32* @leak_pointer(), !dbg !183
  tail call void @llvm.dbg.value(metadata i32* %call, i64 0, metadata !70, metadata !90), !dbg !184
  %call1 = tail call i8* @malloc(i64 4), !dbg !185
  %0 = bitcast i32* %call to i8*, !dbg !186
  %call2 = tail call i32 @test_equal(i8* %0, i8* %call1), !dbg !188
  %tobool = icmp eq i32 %call2, 0, !dbg !188
  br i1 %tobool, label %if.end, label %if.then, !dbg !189

if.then:                                          ; preds = %entry
  %call3 = tail call i32 @puts(i8* nonnull getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i64 0, i64 0)), !dbg !190
  br label %if.end, !dbg !192

if.end:                                           ; preds = %entry, %if.then
  ret i32 1, !dbg !193
}

; Function Attrs: nounwind ssp uwtable
define i32 @lt_after_stack_free() #0 !dbg !72 {
entry:
  %call = tail call i32* @leak_pointer(), !dbg !194
  tail call void @llvm.dbg.value(metadata i32* %call, i64 0, metadata !74, metadata !90), !dbg !195
  %call1 = tail call i32* @leak_pointer(), !dbg !196
  tail call void @llvm.dbg.value(metadata i32* %call1, i64 0, metadata !75, metadata !90), !dbg !197
  %0 = bitcast i32* %call to i8*, !dbg !198
  %1 = bitcast i32* %call1 to i8*, !dbg !200
  %call2 = tail call i32 @test_lt(i8* %0, i8* %1), !dbg !201
  %tobool = icmp eq i32 %call2, 0, !dbg !201
  br i1 %tobool, label %if.end, label %if.then, !dbg !202

if.then:                                          ; preds = %entry
  %call3 = tail call i32 @puts(i8* nonnull getelementptr inbounds ([4 x i8], [4 x i8]* @.str.1, i64 0, i64 0)), !dbg !203
  br label %if.end, !dbg !205

if.end:                                           ; preds = %entry, %if.then
  ret i32 1, !dbg !206
}

; Function Attrs: nounwind ssp uwtable
define i32 @free_global() #0 !dbg !76 {
entry:
  tail call void @llvm.dbg.value(metadata i8* getelementptr inbounds ([6 x i8], [6 x i8]* @global_string, i32 0, i32 0), i64 0, metadata !78, metadata !90), !dbg !207
  tail call void @free(i8* getelementptr inbounds ([6 x i8], [6 x i8]* @global_string, i64 0, i64 0)), !dbg !208
  ret i32 1, !dbg !209
}

; Function Attrs: nounwind readnone
declare void @llvm.dbg.value(metadata, i64, metadata, metadata) #5

attributes #0 = { nounwind ssp uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="core2" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+ssse3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind }
attributes #2 = { nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="core2" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+ssse3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { norecurse nounwind readnone ssp uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="core2" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+ssse3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { norecurse nounwind ssp uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="core2" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+ssse3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { nounwind readnone }
attributes #6 = { nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!85, !86, !87}
!llvm.ident = !{!88}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 3.8.1 (tags/RELEASE_381/final)", isOptimized: true, runtimeVersion: 0, emissionKind: 1, enums: !2, retainedTypes: !3, subprograms: !7, globals: !80)
!1 = !DIFile(filename: "test.c", directory: "/Users/rdockins/code/saw-script/intTests/test0026_bad_pointers")
!2 = !{}
!3 = !{!4, !6}
!4 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !5, size: 64, align: 64)
!5 = !DIBasicType(name: "int", size: 32, align: 32, encoding: DW_ATE_signed)
!6 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64, align: 64)
!7 = !{!8, !15, !18, !21, !27, !31, !34, !41, !45, !51, !54, !57, !60, !65, !68, !72, !76}
!8 = distinct !DISubprogram(name: "read_after_free", scope: !1, file: !1, line: 4, type: !9, isLocal: false, isDefinition: true, scopeLine: 5, isOptimized: true, variables: !11)
!9 = !DISubroutineType(types: !10)
!10 = !{!5}
!11 = !{!12}
!12 = !DILocalVariable(name: "x", scope: !8, file: !1, line: 6, type: !13)
!13 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !14, size: 64, align: 64)
!14 = !DIDerivedType(tag: DW_TAG_volatile_type, baseType: !5)
!15 = distinct !DISubprogram(name: "write_after_free", scope: !1, file: !1, line: 12, type: !9, isLocal: false, isDefinition: true, scopeLine: 13, isOptimized: true, variables: !16)
!16 = !{!17}
!17 = !DILocalVariable(name: "x", scope: !15, file: !1, line: 14, type: !13)
!18 = distinct !DISubprogram(name: "double_free", scope: !1, file: !1, line: 21, type: !9, isLocal: false, isDefinition: true, scopeLine: 22, isOptimized: true, variables: !19)
!19 = !{!20}
!20 = !DILocalVariable(name: "x", scope: !18, file: !1, line: 23, type: !13)
!21 = distinct !DISubprogram(name: "test_equal", scope: !1, file: !1, line: 30, type: !22, isLocal: false, isDefinition: true, scopeLine: 30, flags: DIFlagPrototyped, isOptimized: true, variables: !24)
!22 = !DISubroutineType(types: !23)
!23 = !{!5, !6, !6}
!24 = !{!25, !26}
!25 = !DILocalVariable(name: "x", arg: 1, scope: !21, file: !1, line: 30, type: !6)
!26 = !DILocalVariable(name: "y", arg: 2, scope: !21, file: !1, line: 30, type: !6)
!27 = distinct !DISubprogram(name: "test_lt", scope: !1, file: !1, line: 34, type: !22, isLocal: false, isDefinition: true, scopeLine: 34, flags: DIFlagPrototyped, isOptimized: true, variables: !28)
!28 = !{!29, !30}
!29 = !DILocalVariable(name: "x", arg: 1, scope: !27, file: !1, line: 34, type: !6)
!30 = !DILocalVariable(name: "y", arg: 2, scope: !27, file: !1, line: 34, type: !6)
!31 = distinct !DISubprogram(name: "equals_after_free", scope: !1, file: !1, line: 38, type: !9, isLocal: false, isDefinition: true, scopeLine: 39, isOptimized: true, variables: !32)
!32 = !{!33}
!33 = !DILocalVariable(name: "x", scope: !31, file: !1, line: 40, type: !13)
!34 = distinct !DISubprogram(name: "le_after_free", scope: !1, file: !1, line: 47, type: !9, isLocal: false, isDefinition: true, scopeLine: 48, isOptimized: true, variables: !35)
!35 = !{!36, !40}
!36 = !DILocalVariable(name: "x", scope: !34, file: !1, line: 49, type: !37)
!37 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !38, size: 64, align: 64)
!38 = !DIDerivedType(tag: DW_TAG_volatile_type, baseType: !39)
!39 = !DIBasicType(name: "char", size: 8, align: 8, encoding: DW_ATE_signed_char)
!40 = !DILocalVariable(name: "y", scope: !34, file: !1, line: 50, type: !37)
!41 = distinct !DISubprogram(name: "le_different_allocs", scope: !1, file: !1, line: 56, type: !9, isLocal: false, isDefinition: true, scopeLine: 57, isOptimized: true, variables: !42)
!42 = !{!43, !44}
!43 = !DILocalVariable(name: "x", scope: !41, file: !1, line: 58, type: !13)
!44 = !DILocalVariable(name: "y", scope: !41, file: !1, line: 59, type: !13)
!45 = distinct !DISubprogram(name: "leak_pointer", scope: !1, file: !1, line: 67, type: !46, isLocal: false, isDefinition: true, scopeLine: 68, isOptimized: true, variables: !48)
!46 = !DISubroutineType(types: !47)
!47 = !{!4}
!48 = !{!49, !50}
!49 = !DILocalVariable(name: "x", scope: !45, file: !1, line: 69, type: !14)
!50 = !DILocalVariable(name: "y", scope: !45, file: !1, line: 70, type: !13)
!51 = distinct !DISubprogram(name: "read_after_stack_free", scope: !1, file: !1, line: 75, type: !9, isLocal: false, isDefinition: true, scopeLine: 76, isOptimized: true, variables: !52)
!52 = !{!53}
!53 = !DILocalVariable(name: "x", scope: !51, file: !1, line: 77, type: !4)
!54 = distinct !DISubprogram(name: "write_after_stack_free", scope: !1, file: !1, line: 81, type: !9, isLocal: false, isDefinition: true, scopeLine: 82, isOptimized: true, variables: !55)
!55 = !{!56}
!56 = !DILocalVariable(name: "x", scope: !54, file: !1, line: 83, type: !4)
!57 = distinct !DISubprogram(name: "free_after_stack_free", scope: !1, file: !1, line: 88, type: !9, isLocal: false, isDefinition: true, scopeLine: 89, isOptimized: true, variables: !58)
!58 = !{!59}
!59 = !DILocalVariable(name: "x", scope: !57, file: !1, line: 90, type: !4)
!60 = distinct !DISubprogram(name: "subfn", scope: !1, file: !1, line: 97, type: !61, isLocal: false, isDefinition: true, scopeLine: 97, flags: DIFlagPrototyped, isOptimized: true, variables: !63)
!61 = !DISubroutineType(types: !62)
!62 = !{null, !6}
!63 = !{!64}
!64 = !DILocalVariable(name: "x", arg: 1, scope: !60, file: !1, line: 97, type: !6)
!65 = distinct !DISubprogram(name: "free_local", scope: !1, file: !1, line: 101, type: !9, isLocal: false, isDefinition: true, scopeLine: 102, isOptimized: true, variables: !66)
!66 = !{!67}
!67 = !DILocalVariable(name: "x", scope: !65, file: !1, line: 103, type: !14)
!68 = distinct !DISubprogram(name: "equals_after_stack_free", scope: !1, file: !1, line: 108, type: !9, isLocal: false, isDefinition: true, scopeLine: 109, isOptimized: true, variables: !69)
!69 = !{!70, !71}
!70 = !DILocalVariable(name: "x", scope: !68, file: !1, line: 110, type: !4)
!71 = !DILocalVariable(name: "y", scope: !68, file: !1, line: 111, type: !4)
!72 = distinct !DISubprogram(name: "lt_after_stack_free", scope: !1, file: !1, line: 116, type: !9, isLocal: false, isDefinition: true, scopeLine: 117, isOptimized: true, variables: !73)
!73 = !{!74, !75}
!74 = !DILocalVariable(name: "x", scope: !72, file: !1, line: 118, type: !4)
!75 = !DILocalVariable(name: "y", scope: !72, file: !1, line: 119, type: !4)
!76 = distinct !DISubprogram(name: "free_global", scope: !1, file: !1, line: 125, type: !9, isLocal: false, isDefinition: true, scopeLine: 126, isOptimized: true, variables: !77)
!77 = !{!78}
!78 = !DILocalVariable(name: "x", scope: !76, file: !1, line: 127, type: !79)
!79 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !39, size: 64, align: 64)
!80 = !{!81}
!81 = !DIGlobalVariable(name: "global_string", scope: !0, file: !1, line: 124, type: !82, isLocal: false, isDefinition: true, variable: [6 x i8]* @global_string)
!82 = !DICompositeType(tag: DW_TAG_array_type, baseType: !39, size: 48, align: 8, elements: !83)
!83 = !{!84}
!84 = !DISubrange(count: 6)
!85 = !{i32 2, !"Dwarf Version", i32 2}
!86 = !{i32 2, !"Debug Info Version", i32 3}
!87 = !{i32 1, !"PIC Level", i32 2}
!88 = !{!"clang version 3.8.1 (tags/RELEASE_381/final)"}
!89 = !DILocation(line: 6, column: 21, scope: !8)
!90 = !DIExpression()
!91 = !DILocation(line: 6, column: 17, scope: !8)
!92 = !DILocation(line: 7, column: 6, scope: !8)
!93 = !{!94, !94, i64 0}
!94 = !{!"int", !95, i64 0}
!95 = !{!"omnipotent char", !96, i64 0}
!96 = !{!"Simple C/C++ TBAA"}
!97 = !DILocation(line: 8, column: 3, scope: !8)
!98 = !DILocation(line: 9, column: 10, scope: !8)
!99 = !DILocation(line: 9, column: 3, scope: !8)
!100 = !DILocation(line: 14, column: 21, scope: !15)
!101 = !DILocation(line: 14, column: 17, scope: !15)
!102 = !DILocation(line: 15, column: 6, scope: !15)
!103 = !DILocation(line: 16, column: 3, scope: !15)
!104 = !DILocation(line: 17, column: 6, scope: !15)
!105 = !DILocation(line: 18, column: 3, scope: !15)
!106 = !DILocation(line: 23, column: 21, scope: !18)
!107 = !DILocation(line: 23, column: 17, scope: !18)
!108 = !DILocation(line: 24, column: 6, scope: !18)
!109 = !DILocation(line: 25, column: 3, scope: !18)
!110 = !DILocation(line: 26, column: 3, scope: !18)
!111 = !DILocation(line: 27, column: 3, scope: !18)
!112 = !DILocation(line: 30, column: 23, scope: !21)
!113 = !DILocation(line: 30, column: 32, scope: !21)
!114 = !DILocation(line: 31, column: 13, scope: !21)
!115 = !DILocation(line: 31, column: 3, scope: !21)
!116 = !DILocation(line: 34, column: 20, scope: !27)
!117 = !DILocation(line: 34, column: 29, scope: !27)
!118 = !DILocation(line: 35, column: 13, scope: !27)
!119 = !DILocation(line: 35, column: 3, scope: !27)
!120 = !DILocation(line: 40, column: 21, scope: !31)
!121 = !DILocation(line: 40, column: 17, scope: !31)
!122 = !DILocation(line: 41, column: 6, scope: !31)
!123 = !DILocation(line: 42, column: 3, scope: !31)
!124 = !DILocation(line: 43, column: 7, scope: !125)
!125 = distinct !DILexicalBlock(scope: !31, file: !1, line: 43, column: 7)
!126 = !DILocation(line: 43, column: 7, scope: !31)
!127 = !DILocation(line: 43, column: 45, scope: !128)
!128 = distinct !DILexicalBlock(scope: !125, file: !1, line: 43, column: 43)
!129 = !DILocation(line: 43, column: 58, scope: !128)
!130 = !DILocation(line: 44, column: 3, scope: !31)
!131 = !DILocation(line: 49, column: 22, scope: !34)
!132 = !DILocation(line: 49, column: 18, scope: !34)
!133 = !DILocation(line: 50, column: 24, scope: !34)
!134 = !DILocation(line: 50, column: 18, scope: !34)
!135 = !DILocation(line: 51, column: 3, scope: !34)
!136 = !DILocation(line: 52, column: 7, scope: !137)
!137 = distinct !DILexicalBlock(scope: !34, file: !1, line: 52, column: 7)
!138 = !DILocation(line: 52, column: 7, scope: !34)
!139 = !DILocation(line: 52, column: 43, scope: !140)
!140 = distinct !DILexicalBlock(scope: !137, file: !1, line: 52, column: 41)
!141 = !DILocation(line: 52, column: 56, scope: !140)
!142 = !DILocation(line: 53, column: 3, scope: !34)
!143 = !DILocation(line: 58, column: 21, scope: !41)
!144 = !DILocation(line: 58, column: 17, scope: !41)
!145 = !DILocation(line: 59, column: 21, scope: !41)
!146 = !DILocation(line: 59, column: 17, scope: !41)
!147 = !DILocation(line: 60, column: 6, scope: !41)
!148 = !DILocation(line: 61, column: 6, scope: !41)
!149 = !DILocation(line: 62, column: 7, scope: !150)
!150 = distinct !DILexicalBlock(scope: !41, file: !1, line: 62, column: 7)
!151 = !DILocation(line: 62, column: 7, scope: !41)
!152 = !DILocation(line: 62, column: 43, scope: !153)
!153 = distinct !DILexicalBlock(scope: !150, file: !1, line: 62, column: 41)
!154 = !DILocation(line: 62, column: 56, scope: !153)
!155 = !DILocation(line: 63, column: 3, scope: !41)
!156 = !DILocation(line: 69, column: 3, scope: !45)
!157 = !DILocation(line: 70, column: 17, scope: !45)
!158 = !DILocation(line: 69, column: 16, scope: !45)
!159 = !DILocation(line: 71, column: 6, scope: !45)
!160 = !DILocation(line: 73, column: 1, scope: !45)
!161 = !DILocation(line: 72, column: 3, scope: !45)
!162 = !DILocation(line: 77, column: 13, scope: !51)
!163 = !DILocation(line: 77, column: 9, scope: !51)
!164 = !DILocation(line: 78, column: 10, scope: !51)
!165 = !DILocation(line: 78, column: 3, scope: !51)
!166 = !DILocation(line: 83, column: 13, scope: !54)
!167 = !DILocation(line: 83, column: 9, scope: !54)
!168 = !DILocation(line: 84, column: 6, scope: !54)
!169 = !DILocation(line: 85, column: 3, scope: !54)
!170 = !DILocation(line: 90, column: 13, scope: !57)
!171 = !DILocation(line: 90, column: 9, scope: !57)
!172 = !DILocation(line: 91, column: 8, scope: !57)
!173 = !DILocation(line: 91, column: 3, scope: !57)
!174 = !DILocation(line: 92, column: 3, scope: !57)
!175 = !DILocation(line: 97, column: 18, scope: !60)
!176 = !DILocation(line: 98, column: 3, scope: !60)
!177 = !DILocation(line: 99, column: 1, scope: !60)
!178 = !DILocation(line: 103, column: 3, scope: !65)
!179 = !DILocation(line: 103, column: 16, scope: !65)
!180 = !DILocation(line: 104, column: 3, scope: !65)
!181 = !DILocation(line: 106, column: 1, scope: !65)
!182 = !DILocation(line: 105, column: 3, scope: !65)
!183 = !DILocation(line: 110, column: 13, scope: !68)
!184 = !DILocation(line: 110, column: 9, scope: !68)
!185 = !DILocation(line: 111, column: 13, scope: !68)
!186 = !DILocation(line: 112, column: 19, scope: !187)
!187 = distinct !DILexicalBlock(scope: !68, file: !1, line: 112, column: 7)
!188 = !DILocation(line: 112, column: 7, scope: !187)
!189 = !DILocation(line: 112, column: 7, scope: !68)
!190 = !DILocation(line: 112, column: 30, scope: !191)
!191 = distinct !DILexicalBlock(scope: !187, file: !1, line: 112, column: 28)
!192 = !DILocation(line: 112, column: 43, scope: !191)
!193 = !DILocation(line: 113, column: 3, scope: !68)
!194 = !DILocation(line: 118, column: 13, scope: !72)
!195 = !DILocation(line: 118, column: 9, scope: !72)
!196 = !DILocation(line: 119, column: 13, scope: !72)
!197 = !DILocation(line: 119, column: 9, scope: !72)
!198 = !DILocation(line: 120, column: 16, scope: !199)
!199 = distinct !DILexicalBlock(scope: !72, file: !1, line: 120, column: 7)
!200 = !DILocation(line: 120, column: 19, scope: !199)
!201 = !DILocation(line: 120, column: 7, scope: !199)
!202 = !DILocation(line: 120, column: 7, scope: !72)
!203 = !DILocation(line: 120, column: 27, scope: !204)
!204 = distinct !DILexicalBlock(scope: !199, file: !1, line: 120, column: 25)
!205 = !DILocation(line: 120, column: 40, scope: !204)
!206 = !DILocation(line: 121, column: 3, scope: !72)
!207 = !DILocation(line: 127, column: 9, scope: !76)
!208 = !DILocation(line: 128, column: 3, scope: !76)
!209 = !DILocation(line: 129, column: 3, scope: !76)
