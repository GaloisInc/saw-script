; ModuleID = 'test.c'
target datalayout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx10.13.0"

%struct.a_t = type { i32 }

@bar.s = private unnamed_addr constant [4 x %struct.a_t] [%struct.a_t { i32 1 }, %struct.a_t { i32 2 }, %struct.a_t { i32 3 }, %struct.a_t { i32 4 }], align 16
@.str = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1

; Function Attrs: norecurse nounwind ssp uwtable
define i32 @foo(%struct.a_t* nocapture %s) #0 !dbg !4 {
entry:
  tail call void @llvm.dbg.value(metadata %struct.a_t* %s, i64 0, metadata !16, metadata !33), !dbg !34
  %x = getelementptr inbounds %struct.a_t, %struct.a_t* %s, i64 0, i32 0, !dbg !35
  store i32 3, i32* %x, align 4, !dbg !36, !tbaa !37
  ret i32 3, !dbg !42
}

; Function Attrs: nounwind readnone
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: norecurse nounwind ssp uwtable
define i32 @bar() #0 !dbg !17 {
entry:
  %s = alloca [4 x %struct.a_t], align 16
  %0 = bitcast [4 x %struct.a_t]* %s to i8*, !dbg !43
  call void @llvm.lifetime.start(i64 16, i8* %0) #5, !dbg !43
  tail call void @llvm.dbg.declare(metadata [4 x %struct.a_t]* %s, metadata !21, metadata !33), !dbg !44
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* %0, i8* bitcast ([4 x %struct.a_t]* @bar.s to i8*), i64 16, i32 16, i1 false), !dbg !44
  %arraydecay = getelementptr inbounds [4 x %struct.a_t], [4 x %struct.a_t]* %s, i64 0, i64 0, !dbg !45
  %call = call i32 @foo(%struct.a_t* %arraydecay), !dbg !46
  call void @llvm.lifetime.end(i64 16, i8* %0) #5, !dbg !47
  ret i32 3, !dbg !48
}

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start(i64, i8* nocapture) #2

; Function Attrs: argmemonly nounwind
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture, i8* nocapture readonly, i64, i32, i1) #2

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.end(i64, i8* nocapture) #2

; Function Attrs: nounwind ssp uwtable
define i32 @main() #3 !dbg !25 {
entry:
  %call = tail call i32 @bar(), !dbg !49
  %call1 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i64 0, i64 0), i32 3), !dbg !50
  ret i32 0, !dbg !51
}

; Function Attrs: nounwind
declare i32 @printf(i8* nocapture readonly, ...) #4

; Function Attrs: nounwind readnone
declare void @llvm.dbg.value(metadata, i64, metadata, metadata) #1

attributes #0 = { norecurse nounwind ssp uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="core2" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+ssse3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone }
attributes #2 = { argmemonly nounwind }
attributes #3 = { nounwind ssp uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="core2" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+ssse3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="core2" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+ssse3" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!29, !30, !31}
!llvm.ident = !{!32}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 3.8.1 (tags/RELEASE_381/final)", isOptimized: true, runtimeVersion: 0, emissionKind: 1, enums: !2, subprograms: !3)
!1 = !DIFile(filename: "test.c", directory: "/Users/rdockins/code/saw-script/unit_struct")
!2 = !{}
!3 = !{!4, !17, !25}
!4 = distinct !DISubprogram(name: "foo", scope: !1, file: !1, line: 8, type: !5, isLocal: false, isDefinition: true, scopeLine: 8, flags: DIFlagPrototyped, isOptimized: true, variables: !15)
!5 = !DISubroutineType(types: !6)
!6 = !{!7, !10}
!7 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint32_t", file: !8, line: 31, baseType: !9)
!8 = !DIFile(filename: "/usr/include/_types/_uint32_t.h", directory: "/Users/rdockins/code/saw-script/unit_struct")
!9 = !DIBasicType(name: "unsigned int", size: 32, align: 32, encoding: DW_ATE_unsigned)
!10 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !11, size: 64, align: 64)
!11 = !DIDerivedType(tag: DW_TAG_typedef, name: "a_t", file: !1, line: 6, baseType: !12)
!12 = !DICompositeType(tag: DW_TAG_structure_type, file: !1, line: 4, size: 32, align: 32, elements: !13)
!13 = !{!14}
!14 = !DIDerivedType(tag: DW_TAG_member, name: "x", scope: !12, file: !1, line: 5, baseType: !7, size: 32, align: 32)
!15 = !{!16}
!16 = !DILocalVariable(name: "s", arg: 1, scope: !4, file: !1, line: 8, type: !10)
!17 = distinct !DISubprogram(name: "bar", scope: !1, file: !1, line: 12, type: !18, isLocal: false, isDefinition: true, scopeLine: 12, isOptimized: true, variables: !20)
!18 = !DISubroutineType(types: !19)
!19 = !{!7}
!20 = !{!21}
!21 = !DILocalVariable(name: "s", scope: !17, file: !1, line: 13, type: !22)
!22 = !DICompositeType(tag: DW_TAG_array_type, baseType: !11, size: 128, align: 32, elements: !23)
!23 = !{!24}
!24 = !DISubrange(count: 4)
!25 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 18, type: !26, isLocal: false, isDefinition: true, scopeLine: 18, isOptimized: true, variables: !2)
!26 = !DISubroutineType(types: !27)
!27 = !{!28}
!28 = !DIBasicType(name: "int", size: 32, align: 32, encoding: DW_ATE_signed)
!29 = !{i32 2, !"Dwarf Version", i32 2}
!30 = !{i32 2, !"Debug Info Version", i32 3}
!31 = !{i32 1, !"PIC Level", i32 2}
!32 = !{!"clang version 3.8.1 (tags/RELEASE_381/final)"}
!33 = !DIExpression()
!34 = !DILocation(line: 8, column: 20, scope: !4)
!35 = !DILocation(line: 9, column: 13, scope: !4)
!36 = !DILocation(line: 9, column: 15, scope: !4)
!37 = !{!38, !39, i64 0}
!38 = !{!"", !39, i64 0}
!39 = !{!"int", !40, i64 0}
!40 = !{!"omnipotent char", !41, i64 0}
!41 = !{!"Simple C/C++ TBAA"}
!42 = !DILocation(line: 9, column: 3, scope: !4)
!43 = !DILocation(line: 13, column: 3, scope: !17)
!44 = !DILocation(line: 13, column: 7, scope: !17)
!45 = !DILocation(line: 15, column: 15, scope: !17)
!46 = !DILocation(line: 15, column: 10, scope: !17)
!47 = !DILocation(line: 16, column: 1, scope: !17)
!48 = !DILocation(line: 15, column: 3, scope: !17)
!49 = !DILocation(line: 19, column: 18, scope: !25)
!50 = !DILocation(line: 19, column: 3, scope: !25)
!51 = !DILocation(line: 20, column: 3, scope: !25)
