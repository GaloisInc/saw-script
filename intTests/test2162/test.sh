# Don't exit unexpectedly.
set +e

# Run all three tests so if something goes wrong we can see all the
# output.
echo "*** test1.saw ***"
$SAW test1.saw
R1=$?

echo "*** test2.saw ***"
$SAW test2.saw
R2=$?

echo "*** test3.saw ***"
$SAW test3.saw
R3=$?

EX=0

# t1 should succeed; t2 and t3 should fail
# (until #2167 gets done; until then t2 succeeds with a warning)
if [ $R1 != 0 ]; then
    echo "*** test1.saw failed (exit $R1) ***"
    EX=1
fi
if [ $R2 == 0 ]; then
    echo "*** test2.saw did not fail (exit $R2) ***"
    EX=1
fi
if [ $R3 == 0 ]; then
    echo "*** test3.saw did not fail (exit $R3) ***"
    EX=1
fi

exit $EX
