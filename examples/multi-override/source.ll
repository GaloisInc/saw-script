; ModuleID = 'source.c'
source_filename = "source.c"
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.14.0"

@example_sums.nums = private unnamed_addr constant [10 x i32] [i32 0, i32 1, i32 2, i32 3, i32 4, i32 6, i32 7, i32 8, i32 9, i32 0], align 16
@myglobal = common global i32 0, align 4, !dbg !0

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @identity(i32) #0 !dbg !12 {
  %2 = alloca i32, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !15, metadata !DIExpression()), !dbg !16
  %3 = load i32, i32* %2, align 4, !dbg !17
  ret i32 %3, !dbg !18
}

; Function Attrs: nounwind readnone speculatable
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @example() #0 !dbg !19 {
  %1 = call i32 @identity(i32 1), !dbg !22
  %2 = call i32 @identity(i32 2), !dbg !23
  %3 = add nsw i32 %1, %2, !dbg !24
  ret i32 %3, !dbg !25
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @bad_example() #0 !dbg !26 {
  %1 = call i32 @identity(i32 3), !dbg !27
  ret i32 %1, !dbg !28
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @sum(i32*, i32) #0 !dbg !29 {
  %3 = alloca i32*, align 8
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  store i32* %0, i32** %3, align 8
  call void @llvm.dbg.declare(metadata i32** %3, metadata !34, metadata !DIExpression()), !dbg !35
  store i32 %1, i32* %4, align 4
  call void @llvm.dbg.declare(metadata i32* %4, metadata !36, metadata !DIExpression()), !dbg !37
  call void @llvm.dbg.declare(metadata i32* %5, metadata !38, metadata !DIExpression()), !dbg !39
  store i32 0, i32* %5, align 4, !dbg !39
  call void @llvm.dbg.declare(metadata i32* %6, metadata !40, metadata !DIExpression()), !dbg !42
  store i32 0, i32* %6, align 4, !dbg !42
  br label %7, !dbg !43

; <label>:7:                                      ; preds = %19, %2
  %8 = load i32, i32* %6, align 4, !dbg !44
  %9 = load i32, i32* %4, align 4, !dbg !46
  %10 = icmp slt i32 %8, %9, !dbg !47
  br i1 %10, label %11, label %22, !dbg !48

; <label>:11:                                     ; preds = %7
  %12 = load i32*, i32** %3, align 8, !dbg !49
  %13 = load i32, i32* %6, align 4, !dbg !51
  %14 = sext i32 %13 to i64, !dbg !49
  %15 = getelementptr inbounds i32, i32* %12, i64 %14, !dbg !49
  %16 = load i32, i32* %15, align 4, !dbg !49
  %17 = load i32, i32* %5, align 4, !dbg !52
  %18 = add i32 %17, %16, !dbg !52
  store i32 %18, i32* %5, align 4, !dbg !52
  br label %19, !dbg !53

; <label>:19:                                     ; preds = %11
  %20 = load i32, i32* %6, align 4, !dbg !54
  %21 = add nsw i32 %20, 1, !dbg !54
  store i32 %21, i32* %6, align 4, !dbg !54
  br label %7, !dbg !55, !llvm.loop !56

; <label>:22:                                     ; preds = %7
  %23 = load i32, i32* %5, align 4, !dbg !58
  ret i32 %23, !dbg !59
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @example_sums() #0 !dbg !60 {
  %1 = alloca [10 x i32], align 16
  call void @llvm.dbg.declare(metadata [10 x i32]* %1, metadata !63, metadata !DIExpression()), !dbg !67
  %2 = bitcast [10 x i32]* %1 to i8*, !dbg !67
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* %2, i8* bitcast ([10 x i32]* @example_sums.nums to i8*), i64 40, i32 16, i1 false), !dbg !67
  %3 = getelementptr inbounds [10 x i32], [10 x i32]* %1, i32 0, i32 0, !dbg !68
  %4 = call i32 @sum(i32* %3, i32 10), !dbg !69
  %5 = getelementptr inbounds [10 x i32], [10 x i32]* %1, i32 0, i32 0, !dbg !70
  %6 = getelementptr inbounds i32, i32* %5, i64 2, !dbg !71
  %7 = call i32 @sum(i32* %6, i32 6), !dbg !72
  %8 = add i32 %4, %7, !dbg !73
  ret i32 %8, !dbg !74
}

; Function Attrs: argmemonly nounwind
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture writeonly, i8* nocapture readonly, i64, i32, i1) #2

; Function Attrs: noinline nounwind optnone ssp uwtable
define void @add_myglobal(i32) #0 !dbg !75 {
  %2 = alloca i32, align 4
  store i32 %0, i32* %2, align 4
  call void @llvm.dbg.declare(metadata i32* %2, metadata !78, metadata !DIExpression()), !dbg !79
  %3 = load i32, i32* @myglobal, align 4, !dbg !80
  %4 = load i32, i32* @myglobal, align 4, !dbg !81
  %5 = mul nsw i32 %3, %4, !dbg !82
  store i32 %5, i32* @myglobal, align 4, !dbg !83
  %6 = load i32, i32* %2, align 4, !dbg !84
  %7 = load i32, i32* @myglobal, align 4, !dbg !85
  %8 = add nsw i32 %7, %6, !dbg !85
  store i32 %8, i32* @myglobal, align 4, !dbg !85
  ret void, !dbg !86
}

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @myglobal_example() #0 !dbg !87 {
  store i32 0, i32* @myglobal, align 4, !dbg !88
  call void @add_myglobal(i32 10), !dbg !89
  call void @add_myglobal(i32 20), !dbg !90
  %1 = load i32, i32* @myglobal, align 4, !dbg !91
  ret i32 %1, !dbg !92
}

attributes #0 = { noinline nounwind optnone ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable }
attributes #2 = { argmemonly nounwind }

!llvm.dbg.cu = !{!2}
!llvm.module.flags = !{!7, !8, !9, !10}
!llvm.ident = !{!11}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(name: "myglobal", scope: !2, file: !3, line: 17, type: !6, isLocal: false, isDefinition: true)
!2 = distinct !DICompileUnit(language: DW_LANG_C99, file: !3, producer: "Apple LLVM version 10.0.0 (clang-1000.10.44.2)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !4, globals: !5)
!3 = !DIFile(filename: "source.c", directory: "/Users/rdockins/code/saw-script/examples/multi-override")
!4 = !{}
!5 = !{!0}
!6 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!7 = !{i32 2, !"Dwarf Version", i32 4}
!8 = !{i32 2, !"Debug Info Version", i32 3}
!9 = !{i32 1, !"wchar_size", i32 4}
!10 = !{i32 7, !"PIC Level", i32 2}
!11 = !{!"Apple LLVM version 10.0.0 (clang-1000.10.44.2)"}
!12 = distinct !DISubprogram(name: "identity", scope: !3, file: !3, line: 1, type: !13, isLocal: false, isDefinition: true, scopeLine: 1, flags: DIFlagPrototyped, isOptimized: false, unit: !2, variables: !4)
!13 = !DISubroutineType(types: !14)
!14 = !{!6, !6}
!15 = !DILocalVariable(name: "x", arg: 1, scope: !12, file: !3, line: 1, type: !6)
!16 = !DILocation(line: 1, column: 18, scope: !12)
!17 = !DILocation(line: 1, column: 30, scope: !12)
!18 = !DILocation(line: 1, column: 23, scope: !12)
!19 = distinct !DISubprogram(name: "example", scope: !3, file: !3, line: 2, type: !20, isLocal: false, isDefinition: true, scopeLine: 2, flags: DIFlagPrototyped, isOptimized: false, unit: !2, variables: !4)
!20 = !DISubroutineType(types: !21)
!21 = !{!6}
!22 = !DILocation(line: 2, column: 28, scope: !19)
!23 = !DILocation(line: 2, column: 42, scope: !19)
!24 = !DILocation(line: 2, column: 40, scope: !19)
!25 = !DILocation(line: 2, column: 21, scope: !19)
!26 = distinct !DISubprogram(name: "bad_example", scope: !3, file: !3, line: 3, type: !20, isLocal: false, isDefinition: true, scopeLine: 3, flags: DIFlagPrototyped, isOptimized: false, unit: !2, variables: !4)
!27 = !DILocation(line: 3, column: 32, scope: !26)
!28 = !DILocation(line: 3, column: 25, scope: !26)
!29 = distinct !DISubprogram(name: "sum", scope: !3, file: !3, line: 5, type: !30, isLocal: false, isDefinition: true, scopeLine: 5, flags: DIFlagPrototyped, isOptimized: false, unit: !2, variables: !4)
!30 = !DISubroutineType(types: !31)
!31 = !{!32, !33, !6}
!32 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!33 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !32, size: 64)
!34 = !DILocalVariable(name: "arr", arg: 1, scope: !29, file: !3, line: 5, type: !33)
!35 = !DILocation(line: 5, column: 33, scope: !29)
!36 = !DILocalVariable(name: "n", arg: 2, scope: !29, file: !3, line: 5, type: !6)
!37 = !DILocation(line: 5, column: 42, scope: !29)
!38 = !DILocalVariable(name: "acc", scope: !29, file: !3, line: 6, type: !32)
!39 = !DILocation(line: 6, column: 22, scope: !29)
!40 = !DILocalVariable(name: "i", scope: !41, file: !3, line: 7, type: !6)
!41 = distinct !DILexicalBlock(scope: !29, file: !3, line: 7, column: 9)
!42 = !DILocation(line: 7, column: 18, scope: !41)
!43 = !DILocation(line: 7, column: 14, scope: !41)
!44 = !DILocation(line: 7, column: 25, scope: !45)
!45 = distinct !DILexicalBlock(scope: !41, file: !3, line: 7, column: 9)
!46 = !DILocation(line: 7, column: 29, scope: !45)
!47 = !DILocation(line: 7, column: 27, scope: !45)
!48 = !DILocation(line: 7, column: 9, scope: !41)
!49 = !DILocation(line: 8, column: 20, scope: !50)
!50 = distinct !DILexicalBlock(scope: !45, file: !3, line: 7, column: 37)
!51 = !DILocation(line: 8, column: 24, scope: !50)
!52 = !DILocation(line: 8, column: 17, scope: !50)
!53 = !DILocation(line: 9, column: 9, scope: !50)
!54 = !DILocation(line: 7, column: 33, scope: !45)
!55 = !DILocation(line: 7, column: 9, scope: !45)
!56 = distinct !{!56, !48, !57}
!57 = !DILocation(line: 9, column: 9, scope: !41)
!58 = !DILocation(line: 10, column: 16, scope: !29)
!59 = !DILocation(line: 10, column: 9, scope: !29)
!60 = distinct !DISubprogram(name: "example_sums", scope: !3, file: !3, line: 12, type: !61, isLocal: false, isDefinition: true, scopeLine: 12, flags: DIFlagPrototyped, isOptimized: false, unit: !2, variables: !4)
!61 = !DISubroutineType(types: !62)
!62 = !{!32}
!63 = !DILocalVariable(name: "nums", scope: !60, file: !3, line: 13, type: !64)
!64 = !DICompositeType(tag: DW_TAG_array_type, baseType: !32, size: 320, elements: !65)
!65 = !{!66}
!66 = !DISubrange(count: 10)
!67 = !DILocation(line: 13, column: 22, scope: !60)
!68 = !DILocation(line: 14, column: 20, scope: !60)
!69 = !DILocation(line: 14, column: 16, scope: !60)
!70 = !DILocation(line: 14, column: 36, scope: !60)
!71 = !DILocation(line: 14, column: 40, scope: !60)
!72 = !DILocation(line: 14, column: 32, scope: !60)
!73 = !DILocation(line: 14, column: 30, scope: !60)
!74 = !DILocation(line: 14, column: 9, scope: !60)
!75 = distinct !DISubprogram(name: "add_myglobal", scope: !3, file: !3, line: 19, type: !76, isLocal: false, isDefinition: true, scopeLine: 19, flags: DIFlagPrototyped, isOptimized: false, unit: !2, variables: !4)
!76 = !DISubroutineType(types: !77)
!77 = !{null, !6}
!78 = !DILocalVariable(name: "x", arg: 1, scope: !75, file: !3, line: 19, type: !6)
!79 = !DILocation(line: 19, column: 23, scope: !75)
!80 = !DILocation(line: 19, column: 39, scope: !75)
!81 = !DILocation(line: 19, column: 50, scope: !75)
!82 = !DILocation(line: 19, column: 48, scope: !75)
!83 = !DILocation(line: 19, column: 37, scope: !75)
!84 = !DILocation(line: 19, column: 72, scope: !75)
!85 = !DILocation(line: 19, column: 69, scope: !75)
!86 = !DILocation(line: 19, column: 75, scope: !75)
!87 = distinct !DISubprogram(name: "myglobal_example", scope: !3, file: !3, line: 20, type: !20, isLocal: false, isDefinition: true, scopeLine: 20, flags: DIFlagPrototyped, isOptimized: false, unit: !2, variables: !4)
!88 = !DILocation(line: 21, column: 12, scope: !87)
!89 = !DILocation(line: 22, column: 3, scope: !87)
!90 = !DILocation(line: 23, column: 3, scope: !87)
!91 = !DILocation(line: 24, column: 10, scope: !87)
!92 = !DILocation(line: 24, column: 3, scope: !87)
