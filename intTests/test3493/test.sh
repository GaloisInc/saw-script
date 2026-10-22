# Check that the Rocq exporter honors CRYPTOLPATH.
#
# Note: intentionally not in saw-core-rocq-tests, because:
#    - there is no need to check the output, it's trivial;
#    - the saw-core-rocq-tests driver doesn't have a way to set
#      environment variables;
#    - we'd like to test both with and without the setting, which
#      it also doesn't know how to do.

# it should fail without CRYPTOLPATH set
echo "*** Without CRYPTOLPATH **"
${SAW:-saw} test.saw && exit 1

# and it should succeed with
echo "*** With CRYPTOLPATH ***"
CRYPTOLPATH=zoo ${SAW:-saw} test.saw || exit 1
