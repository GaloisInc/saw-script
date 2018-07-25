make Stat.class
make Dyn.class
make Sub.class
javap -c Sub
cabal new-exec saw sub_crucible.saw

