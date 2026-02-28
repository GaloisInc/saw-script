$SAW test.saw

echo Checking results against expected...
diff skel_direct.exp skel_direct
diff skel_builtins.exp skel_builtins

