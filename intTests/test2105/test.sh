# Don't exit unexpectedly.
set +e

# Run both tests so if something goes wrong we can see all the output.
echo "*** test1.saw ***"
$SAW test1.saw
R1=$?

echo "*** test2.saw ***"
$SAW test2.saw
R2=$?

EX=0

# both should fail
if [ $R1 == 0 ]; then
    echo "*** test1.saw did not fail (exit $R1) ***"
    EX=1
fi
if [ $R2 == 0 ]; then
    echo "*** test2.saw did not fail (exit $R2) ***"
    EX=1
fi

exit $EX
