## rt.jar file
RTJAR=/Library/Java/JavaVirtualMachines/jdk1.8.0_171.jdk/Contents/Home/jre/lib/rt.jar
make Stat.class
make Dyn.class
make Sub.class
make Arr.class
make Obj.class
make TestStr.class
javap -c TestStr.class
cabal new-exec saw -- -j $RTJAR stat_crucible.saw
cabal new-exec saw -- -j $RTJAR dyn_crucible.saw
cabal new-exec saw -- -j $RTJAR sub_crucible.saw
# cabal new-exec saw -- -j $RTJAR arr_crucible.saw
# cabal new-exec saw -- -j $RTJAR teststr_crucible.saw


