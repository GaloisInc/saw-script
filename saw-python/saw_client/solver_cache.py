import cbor2
from collections.abc import MutableMapping
from dataclasses import dataclass
from datetime import datetime, timezone
import dateutil.parser
import lmdb # type: ignore
import os
from typing import Dict, List, Optional, Tuple, Union
from typing_extensions import Literal

# Adapted from src/SAWScript/SolverCache.hs
SolverBackend = Union[
  Literal["What4"],
  Literal["SBV"],
  Literal["AIG"],
  Literal["RME"],
  # External solvers supported by SBV (adapted from SBV.Solver)
  Literal["ABC"],
  Literal["Boolector"],
  Literal["Bitwuzla"],
  Literal["CVC5"],
  Literal["DReal"], # NOTE: Not currently supported by SAW
  Literal["MathSAT"],
  Literal["Yices"],
  Literal["Z3"]]

@dataclass
class SolverCacheEntry:
  counterexamples : Optional[List[List]]
  solver_name : str
  solver_versions : Dict[SolverBackend, str]
  solver_options : List[List]
  timestamp : datetime

  def __post_init__(self):
    if self.counterexamples is not None:
      if not isinstance(self.counterexamples, list) or \
         any(not isinstance(cex, list) for cex in self.counterexamples):
          raise ValueError('`counterexamples` must be a list of lists')
    if not isinstance(self.solver_name, str):
      raise ValueError('`solver_name` must be a string')
    if not isinstance(self.solver_versions, dict) or \
       any(not isinstance(k, str) or not isinstance(v, str) for k,v in self.solver_versions.items()):
        raise ValueError('`solver_versions` must be a `dict` with `str` keys and values')
    if self.solver_options is not None:
      if not isinstance(self.solver_options, list) or \
         any(not isinstance(opt, list) for opt in self.solver_options):
            raise ValueError('`solver_options` must be a list of lists')
    if not isinstance(self.timestamp, datetime):
      raise ValueError('`timestamp` must be a `datetime` object')

def load_solver_cache_entry(enc):
  obj = cbor2.loads(enc)
  opts = obj['opts'] if 'opts' in obj else []
  t = dateutil.parser.isoparse(obj['t'])
  return SolverCacheEntry(obj.get('cexs'), obj['nm'], obj['vs'], opts, t)

def solver_cache_entry_encoder(encoder, entry):
  if not isinstance(entry, SolverCacheEntry):
      raise Exception('cannot serialize type %s' % entry.__class__)
  entry.__post_init__() # re-validate everything just to be sure
  obj = {} # this dict should be created in alphabetical order to match the Haskell
  if entry.counterexamples is not None: obj['cexs'] = entry.counterexamples
  obj['nm'] = entry.solver_name
  if len(entry.solver_options) > 0: obj['opts'] = entry.solver_options
  obj['t'] = entry.timestamp.astimezone(timezone.utc).isoformat('T').replace('+00:00', 'Z')
  obj['vs'] = entry.solver_versions
  return encoder.encode(obj)

class SolverCache(MutableMapping):
  """An interface for interacting with a SAW solver cache. This is implemented
     as a `MutableMapping` from a 256-bit `bytes` keys to `SolverCacheEntry`
     values, with LMDB as the backend."""

  def __init__(self, path : Optional[str] = None):
    """Immediately open a solver cache at the given path, or if no path is
       given, at the path specified by the current value of the
       `SAW_SOLVER_CACHE_PATH` environment variable. If neither the former is
       given nor the latter is set, a `ValueError` is raised."""
    if path is None:
      if 'SAW_SOLVER_CACHE_PATH' not in os.environ or os.environ['SAW_SOLVER_CACHE_PATH'] == '':
        raise ValueError("no path given to SolverCache and SAW_SOLVER_CACHE_PATH not set")
      path = os.environ['SAW_SOLVER_CACHE_PATH']
    self.env = lmdb.Environment(path, map_size = 4 * 1073741824) # 4 GiB
    self.path = path

  def __len__(self):
    with self.env.begin() as txn:
      return txn.stat()['entries']

  def __getitem__(self, k : bytes):
    if not isinstance(k, bytes) or len(k) != 32:
      raise ValueError("solver cache key must be a 256-bit `bytes` value")
    with self.env.begin() as txn:
      v = txn.get(cbor2.dumps(k))
      if v is None: raise KeyError
      return load_solver_cache_entry(v)

  def __setitem__(self, k : bytes, v : SolverCacheEntry):
    if not isinstance(k, bytes) or len(k) != 32:
      raise ValueError("solver cache key must be a 256-bit `bytes` value")
    if not isinstance(v, SolverCacheEntry):
      raise ValueError("solver cache value must be a `SolverCacheEntry` object")
    with self.env.begin(write = True) as txn:
      txn.put(cbor2.dumps(k), cbor2.dumps(v, default=solver_cache_entry_encoder), overwrite=True)

  def __delitem__(self, k : bytes):
    if not isinstance(k, bytes) or len(k) != 32:
      raise ValueError("solver cache key must be a 256-bit `bytes` value")
    with self.env.begin(write = True) as txn:
      txn.delete(cbor2.dumps(k))

  def _iter(self, keys, values, fn):
    with self.env.begin() as txn:
      with txn.cursor() as curs:
        for v in curs.iternext(keys, values):
          yield fn(v)

  def __iter__(self): yield from self._iter(True,  False, cbor2.loads)
  def keys    (self): yield from self._iter(True,  False, cbor2.loads)
  def values  (self): yield from self._iter(False, True,  load_solver_cache_entry)
  def items   (self): yield from self._iter(True,  True,  lambda kv: (cbor2.loads(kv[0]), load_solver_cache_entry(kv[1])))
