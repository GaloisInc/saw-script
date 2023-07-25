set -e

# Testing the basic features of the solver cache
SAW_SOLVER_CACHE_PATH="test_solver_cache.cache" $SAW test_basics.saw

# Testing the `set_solver_cache_path` command as well as re-using a cache file
$SAW test_path_and_reuse.saw

# Testing cleaning the solver cache
python3 -i ../../saw-remote-api/python/saw_client/solver_cache.py << END
cache = SolverCache("test_solver_cache.cache")
for k,v in cache.items():
  if 'SBV' in v.solver_versions:
    v.solver_versions['SBV'] = '[OLD VERSION]'
    cache[k] = v

END
$SAW test_clean.saw

# Testing that the envionment variable only creates the cache file when needed
rm -rf test_solver_cache.cache
SAW_SOLVER_CACHE_PATH="test_solver_cache.cache" $SAW test_env_var.saw
if [ -d "test_solver_cache.cache" ]; then
  echo "FAILURE: Cache file created from SAW_SOLVER_CACHE_PATH when not used"; exit 1
else
  echo "SUCCESS: Cache file not created from SAW_SOLVER_CACHE_PATH when not used"
fi
