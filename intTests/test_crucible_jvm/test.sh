make Stat.class
make Dyn.class
javap -c Stat
cabal new-exec saw stat_crucible.saw
cabal new-exec saw dyn_crucible.saw
cabal new-exec saw statdyn_crucible.saw
