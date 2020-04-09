; ModuleID = 'test.bc'
source_filename = "test.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.A = type { %struct.B }
%struct.B = type { i32 }

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define %struct.A* @make_A(i32) #0 !dbg !8 {
  %2 = alloca %struct.B, align 4
  %3 = alloca %struct.A*, align 8
  %4 = getelementptr inbounds %struct.B, %struct.B* %2, i32 0, i32 0
  store i32 %0, i32* %4, align 4
  call void @llvm.dbg.declare(metadata %struct.B* %2, metadata !21, metadata !DIExpression()), !dbg !22
  call void @llvm.dbg.declare(metadata %struct.A** %3, metadata !23, metadata !DIExpression()), !dbg !24
  %5 = call noalias i8* @malloc(i64 4) #4, !dbg !25
  %6 = bitcast i8* %5 to %struct.A*, !dbg !25
  store %struct.A* %6, %struct.A** %3, align 8, !dbg !24
  %7 = load %struct.A*, %struct.A** %3, align 8, !dbg !26
  %8 = getelementptr inbounds %struct.A, %struct.A* %7, i32 0, i32 0, !dbg !27
  %9 = bitcast %struct.B* %8 to i8*, !dbg !28
  %10 = bitcast %struct.B* %2 to i8*, !dbg !28
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %9, i8* align 4 %10, i64 4, i1 false), !dbg !28
  %11 = load %struct.A*, %struct.A** %3, align 8, !dbg !29
  ret %struct.A* %11, !dbg !30
}

; Function Attrs: nounwind readnone speculatable
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: nounwind
declare noalias i8* @malloc(i64) #2

; Function Attrs: argmemonly nounwind
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture writeonly, i8* nocapture readonly, i64, i1) #3

attributes #0 = { noinline nounwind optnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone speculatable }
attributes #2 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="4" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { argmemonly nounwind }
attributes #4 = { nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4, !5, !6}
!llvm.ident = !{!7}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 7.0.1 (tags/RELEASE_701/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2)
!1 = !DIFile(filename: "test.c", directory: "/home/siddharthist/code/tmp/alloc")
!2 = !{}
!3 = !{i32 2, !"Dwarf Version", i32 4}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{i32 7, !"PIC Level", i32 2}
!7 = !{!"clang version 7.0.1 (tags/RELEASE_701/final)"}
!8 = distinct !DISubprogram(name: "make_A", scope: !1, file: !1, line: 16, type: !9, isLocal: false, isDefinition: true, scopeLine: 16, flags: DIFlagPrototyped, isOptimized: false, unit: !0, retainedNodes: !2)
!9 = !DISubroutineType(types: !10)
!10 = !{!11, !16}
!11 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !12, size: 64)
!12 = !DIDerivedType(tag: DW_TAG_typedef, name: "A_t", file: !1, line: 14, baseType: !13)
!13 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "A", file: !1, line: 12, size: 32, elements: !14)
!14 = !{!15}
!15 = !DIDerivedType(tag: DW_TAG_member, name: "b", scope: !13, file: !1, line: 13, baseType: !16, size: 32)
!16 = !DIDerivedType(tag: DW_TAG_typedef, name: "B_t", file: !1, line: 10, baseType: !17)
!17 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "B", file: !1, line: 8, size: 32, elements: !18)
!18 = !{!19}
!19 = !DIDerivedType(tag: DW_TAG_member, name: "x", scope: !17, file: !1, line: 9, baseType: !20, size: 32)
!20 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!21 = !DILocalVariable(name: "b", arg: 1, scope: !8, file: !1, line: 16, type: !16)
!22 = !DILocation(line: 16, column: 17, scope: !8)
!23 = !DILocalVariable(name: "ptr", scope: !8, file: !1, line: 17, type: !11)
!24 = !DILocation(line: 17, column: 8, scope: !8)
!25 = !DILocation(line: 17, column: 14, scope: !8)
!26 = !DILocation(line: 18, column: 3, scope: !8)
!27 = !DILocation(line: 18, column: 8, scope: !8)
!28 = !DILocation(line: 18, column: 12, scope: !8)
!29 = !DILocation(line: 19, column: 10, scope: !8)
!30 = !DILocation(line: 19, column: 3, scope: !8)
