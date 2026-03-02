echo running saw
$SAW test.saw

echo Checking results against expected...
diff skel_direct.exp skel_direct
diff skel_builtins.exp skel_builtins

echo Verifying direct output is ingestible
$SAW test_direct.saw

echo Verifying builtins output is ingestible
$SAW test_builtins.saw
