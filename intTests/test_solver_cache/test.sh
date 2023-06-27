set -e

# Testing the basic features of the solver cache
$SAW test_basics.saw

# Make sure Python lmdb bindings are installed
pip install lmdb

# Testing setting a path for the solver cache
$SAW test_path_first.saw
$SAW test_path_second.saw

# Testing setting the solver cache path through an envionment variable
SAW_SOLVER_CACHE_PATH="test.cache" $SAW test_env_var.saw

# Testing cleaning the solver cache
python3 ../../src/SAWScript/SolverCache/lmdb_opt_database.py shell << END
db = LMDBOptDatabase()
db.setPath('test.cache')
for k,v in db.items():
  v_obj = json.loads(v)
  if 'SBV' in v_obj['vs']:
    v_obj['vs']['SBV'] = '[OLD VERSION]'
    db[k] = bytes(json.dumps(v_obj), 'utf-8')

END
$SAW test_clean.saw

# Clean up
rm -rf test.cache
