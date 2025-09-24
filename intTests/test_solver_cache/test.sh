set -e

# Testing the basic features of the solver cache
SAW_SOLVER_CACHE_PATH="test_solver_cache.cache" $SAW test_basics.saw

# Testing the `set_solver_cache_path` command as well as re-using a cache file
$SAW test_path_and_reuse.saw

# Testing the `clean_mismatched_versions_solver_cache` command by manually
# altering the version string of all SBV entries in the database, then running
# `clean_mismatched_versions_solver_cache`
VENV="./test-venv"
mkdir $VENV
python3 -m venv $VENV
source $VENV/bin/activate
python3 -m pip install cbor2 lmdb
python3 -m lmdb -e test_solver_cache.cache shell << END
import cbor2
with ENV.begin(write=True) as txn:
  for k_enc, v_enc in txn.cursor():
    k, v = cbor2.loads(k_enc), cbor2.loads(v_enc)
    if 'vs' in v and 'SBV' in v['vs']:
      v['vs']['SBV'] = '[OLD VERSION]'
      txn.put(k_enc, cbor2.dumps(v))
      print(f'Altered {k.hex()} {v}')
    else:
      print(f'Keeping {k.hex()} {v}')

END
deactivate  # a `venv`-specific function provided by sourcing `$VENV/bin/activate` above
rm -rf $VENV
$SAW test_clean.saw

# Testing that the envionment variable only creates the cache file when needed
rm -rf test_solver_cache.cache
SAW_SOLVER_CACHE_PATH="test_solver_cache.cache" $SAW test_env_var.saw
if [ -d "test_solver_cache.cache" ]; then
  echo "FAILURE: Cache file created from SAW_SOLVER_CACHE_PATH when not used"; exit 1
else
  echo "SUCCESS: Cache file not created from SAW_SOLVER_CACHE_PATH when not used"
fi
