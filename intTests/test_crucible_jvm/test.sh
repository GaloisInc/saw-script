## location of rt.jar file
## this will probably need to change for your system
RTJAR=/Library/Java/JavaVirtualMachines/jdk1.8.0_171.jdk/Contents/Home/jre/lib/rt.jar
SAW="cabal new-exec saw -- "

make Stat.class
make Dyn.class
make Sub.class
make Arr.class
make Obj.class

$SAW --jars $RTJAR stat_crucible.saw
$SAW --jars $RTJAR dyn_crucible.saw
$SAW --jars $RTJAR sub_crucible.saw
$SAW --jars $RTJAR teststr_crucible.saw


