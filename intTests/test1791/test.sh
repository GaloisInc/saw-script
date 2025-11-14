set -e

# inputs

$SAW paths01/test.saw
$SAW paths02/test.saw
$SAW paths03/test.saw

# outputs
# these are all just different enough to be annoying

$SAW -s paths04.summary paths04/test.saw
if [ -f paths04/paths04.summary ]; then
    echo "$0: paths04.summary appeared in the subdir" 1>&2
    exit 1
fi
if ! [ -f paths04.summary ]; then
    echo "$0: paths04.summary did not appear" 1>&2
    exit 1
fi
rm -f paths04.summary

$SAW paths05/test.saw
if [ -f paths05.smt ]; then
    echo "$0: paths05.smt appeared in the top dir" 1>&2
    exit 1
fi
if ! [ -f paths05/paths05.smt ]; then
    echo "$0: paths05/paths05.smt did not appear" 1>&2
    exit 1
fi
rm -f paths05/paths05.smt

$SAW paths06/test.saw
if [ -f paths06.v ]; then
    echo "$0: paths06.v appeared in the top dir" 1>&2
    exit 1
fi
if ! [ -f paths06/paths06.v ]; then
    echo "$0: paths06/paths06.v did not appear" 1>&2
    exit 1
fi
rm -f paths06/paths06.v

$SAW paths07/test.saw
if [ -f paths07.prove0.smt2 ]; then
    echo "$0: paths07.prove0.smt2 appeared in the top dir" 1>&2
    exit 1
fi
if ! [ -f paths07/paths07.prove0.smt2 ]; then
    echo "$0: paths07/paths07.prove0.smt2 did not appear" 1>&2
    exit 1
fi
rm -f paths07/paths07.prove0.smt2
