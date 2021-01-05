set -e

# The '$JSS' command is defined to 'eval', so we need an extra level
# of quoting to protect the semicolons in the classpath on Windows.
$JSS -c "'a${CPSEP}b'" org/example/Test
$JSS -c "'a${CPSEP}b'" com/example/Test

# These should timeout for JSS where
# https://github.com/GaloisInc/jvm-verifier/issues/3 is not fixed,
# since JSS will attempt to load all '.class' files it can find at or
# below the root directory.
if [ "${OS}" == "Windows_NT" ]; then
    BASE=$(cygpath -w "$(pwd)")
else
    BASE=$(pwd)
fi
cp=${BASE}${DIRSEP}a${CPSEP}${BASE}${DIRSEP}b${CPSEP}.
sawfile=${BASE}${DIRSEP}test.saw
rm -rf tmp?
(mkdir tmp1 && cd tmp1 && $JSS -c "'$cp'" org/example/Test)
(mkdir tmp2 && cd tmp2 && $JSS -c "'$cp'" com/example/Test)
(mkdir tmp3 && cd tmp3 && $SAW -c "'$cp'" "'$sawfile'")
