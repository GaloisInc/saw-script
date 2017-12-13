; ModuleID = 'test.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.13.0"

; Function Attrs: nounwind ssp uwtable
define void @clear_void(i8* %arr, i32 %size) #0 !dbg !4 {
entry:
  %arr.addr = alloca i8*, align 8
  %size.addr = alloca i32, align 4
  %cArr = alloca i8*, align 8
  %i = alloca i32, align 4
  store i8* %arr, i8** %arr.addr, align 8
  call void @llvm.dbg.declare(metadata i8** %arr.addr, metadata !17, metadata !18), !dbg !19
  store i32 %size, i32* %size.addr, align 4
  call void @llvm.dbg.declare(metadata i32* %size.addr, metadata !20, metadata !18), !dbg !21
  call void @llvm.dbg.declare(metadata i8** %cArr, metadata !22, metadata !18), !dbg !25
  %0 = load i8*, i8** %arr.addr, align 8, !dbg !26
  store i8* %0, i8** %cArr, align 8, !dbg !25
  call void @llvm.dbg.declare(metadata i32* %i, metadata !27, metadata !18), !dbg !30
  store i32 0, i32* %i, align 4, !dbg !30
  br label %for.cond, !dbg !31

for.cond:                                         ; preds = %for.inc, %entry
  %1 = load i32, i32* %i, align 4, !dbg !32
  %2 = load i32, i32* %size.addr, align 4, !dbg !34
  %cmp = icmp ult i32 %1, %2, !dbg !35
  br i1 %cmp, label %for.body, label %for.end, !dbg !36

for.body:                                         ; preds = %for.cond
  %3 = load i32, i32* %i, align 4, !dbg !37
  %idxprom = sext i32 %3 to i64, !dbg !39
  %4 = load i8*, i8** %cArr, align 8, !dbg !39
  %arrayidx = getelementptr inbounds i8, i8* %4, i64 %idxprom, !dbg !39
  store i8 0, i8* %arrayidx, align 1, !dbg !40
  br label %for.inc, !dbg !41

for.inc:                                          ; preds = %for.body
  %5 = load i32, i32* %i, align 4, !dbg !42
  %inc = add nsw i32 %5, 1, !dbg !42
  store i32 %inc, i32* %i, align 4, !dbg !42
  br label %for.cond, !dbg !43

for.end:                                          ; preds = %for.cond
  ret void, !dbg !44
}

; Function Attrs: nounwind readnone
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: nounwind ssp uwtable
define void @clear_uints(i32* %uints, i32 %numUInts) #0 !dbg !9 {
entry:
  %uints.addr = alloca i32*, align 8
  %numUInts.addr = alloca i32, align 4
  store i32* %uints, i32** %uints.addr, align 8
  call void @llvm.dbg.declare(metadata i32** %uints.addr, metadata !45, metadata !18), !dbg !46
  store i32 %numUInts, i32* %numUInts.addr, align 4
  call void @llvm.dbg.declare(metadata i32* %numUInts.addr, metadata !47, metadata !18), !dbg !48
  %0 = load i32*, i32** %uints.addr, align 8, !dbg !49
  %1 = bitcast i32* %0 to i8*, !dbg !49
  %2 = load i32, i32* %numUInts.addr, align 4, !dbg !50
  %conv = zext i32 %2 to i64, !dbg !50
  %mul = mul i64 %conv, 4, !dbg !51
  %conv1 = trunc i64 %mul to i32, !dbg !50
  call void @clear_void(i8* %1, i32 %conv1), !dbg !52
  ret void, !dbg !53
}

attributes #0 = { nounwind ssp uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="core2" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+ssse3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!13, !14, !15}
!llvm.ident = !{!16}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 3.8.1 (tags/RELEASE_381/final)", isOptimized: false, runtimeVersion: 0, emissionKind: 1, enums: !2, subprograms: !3)
!1 = !DIFile(filename: "test.c", directory: "/Users/rdockins/code/saw-script/intTests/test0029")
!2 = !{}
!3 = !{!4, !9}
!4 = distinct !DISubprogram(name: "clear_void", scope: !1, file: !1, line: 4, type: !5, isLocal: false, isDefinition: true, scopeLine: 4, flags: DIFlagPrototyped, isOptimized: false, variables: !2)
!5 = !DISubroutineType(types: !6)
!6 = !{null, !7, !8}
!7 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64, align: 64)
!8 = !DIBasicType(name: "unsigned int", size: 32, align: 32, encoding: DW_ATE_unsigned)
!9 = distinct !DISubprogram(name: "clear_uints", scope: !1, file: !1, line: 12, type: !10, isLocal: false, isDefinition: true, scopeLine: 12, flags: DIFlagPrototyped, isOptimized: false, variables: !2)
!10 = !DISubroutineType(types: !11)
!11 = !{null, !12, !8}
!12 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !8, size: 64, align: 64)
!13 = !{i32 2, !"Dwarf Version", i32 2}
!14 = !{i32 2, !"Debug Info Version", i32 3}
!15 = !{i32 1, !"PIC Level", i32 2}
!16 = !{!"clang version 3.8.1 (tags/RELEASE_381/final)"}
!17 = !DILocalVariable(name: "arr", arg: 1, scope: !4, file: !1, line: 4, type: !7)
!18 = !DIExpression()
!19 = !DILocation(line: 4, column: 23, scope: !4)
!20 = !DILocalVariable(name: "size", arg: 2, scope: !4, file: !1, line: 4, type: !8)
!21 = !DILocation(line: 4, column: 41, scope: !4)
!22 = !DILocalVariable(name: "cArr", scope: !4, file: !1, line: 5, type: !23)
!23 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !24, size: 64, align: 64)
!24 = !DIBasicType(name: "unsigned char", size: 8, align: 8, encoding: DW_ATE_unsigned_char)
!25 = !DILocation(line: 5, column: 20, scope: !4)
!26 = !DILocation(line: 5, column: 27, scope: !4)
!27 = !DILocalVariable(name: "i", scope: !28, file: !1, line: 6, type: !29)
!28 = distinct !DILexicalBlock(scope: !4, file: !1, line: 6, column: 5)
!29 = !DIBasicType(name: "int", size: 32, align: 32, encoding: DW_ATE_signed)
!30 = !DILocation(line: 6, column: 14, scope: !28)
!31 = !DILocation(line: 6, column: 10, scope: !28)
!32 = !DILocation(line: 6, column: 21, scope: !33)
!33 = distinct !DILexicalBlock(scope: !28, file: !1, line: 6, column: 5)
!34 = !DILocation(line: 6, column: 25, scope: !33)
!35 = !DILocation(line: 6, column: 23, scope: !33)
!36 = !DILocation(line: 6, column: 5, scope: !28)
!37 = !DILocation(line: 7, column: 14, scope: !38)
!38 = distinct !DILexicalBlock(scope: !33, file: !1, line: 6, column: 36)
!39 = !DILocation(line: 7, column: 9, scope: !38)
!40 = !DILocation(line: 7, column: 17, scope: !38)
!41 = !DILocation(line: 8, column: 5, scope: !38)
!42 = !DILocation(line: 6, column: 32, scope: !33)
!43 = !DILocation(line: 6, column: 5, scope: !33)
!44 = !DILocation(line: 9, column: 1, scope: !4)
!45 = !DILocalVariable(name: "uints", arg: 1, scope: !9, file: !1, line: 12, type: !12)
!46 = !DILocation(line: 12, column: 32, scope: !9)
!47 = !DILocalVariable(name: "numUInts", arg: 2, scope: !9, file: !1, line: 12, type: !8)
!48 = !DILocation(line: 12, column: 52, scope: !9)
!49 = !DILocation(line: 13, column: 16, scope: !9)
!50 = !DILocation(line: 13, column: 23, scope: !9)
!51 = !DILocation(line: 13, column: 32, scope: !9)
!52 = !DILocation(line: 13, column: 5, scope: !9)
!53 = !DILocation(line: 14, column: 1, scope: !9)
