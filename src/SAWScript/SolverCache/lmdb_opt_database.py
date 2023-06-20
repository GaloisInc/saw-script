from collections.abc import MutableMapping
import json
import sys

def mismatchedJSONObjValues(obj1, obj2):
  """A generator which, given two JSON-serializable objects, yields a sequence
     of pairs of JSON-serailizable objects which indicate which object values
     are mismatched between the two objects. This is done recursively on
     sub-objects and keys which are present in one object but not the other
     are ignored.
     Example
     -------
     >>> list(mismatchedJSONObjValues({'a': 4, 'b': {'c': 5}, 'd': 6 },
                                      {'a': 3, 'b': {'c': 2, 'z': 1}, 'd': 6}))
     [ ({'a': 4}, {'a': 3}), ({'b': {'c': 5}}, {'b': {'c': 2}}) ]
     """
  if isinstance(obj1, dict) and isinstance(obj2, dict):
    for k in obj1.keys() & obj2.keys():
      for ms1, ms2 in mismatchedJSONObjValues(obj1[k], obj2[k]):
        yield {k: ms1}, {k: ms2}
  elif obj1 != obj2:
    yield obj1, obj2

# ------------------------------------------------------------------------------
# A Database optionally backed by LMDB
# ------------------------------------------------------------------------------

class LMDBOptDatabase(MutableMapping):
  """A key-value database which is either implemented as a Python ``dict``, or
    if the user has supplied a path (see ``setPath``/``getPath``), as an LMDB
    database. Keys and values are represented as ``bytes``."""
  
  def __init__(self):
    """Create an empty database with no set path, implemented as a ``dict``"""
    self._path = None
    self._impl = {}
  
  def setPath(self, path, map_size = 10):
    """Open an LMDB database at the given ``path`` with the given ``map_size``,
       add all current entries in the database to the LMDB database, then
       set the current implementation of this database to be the LMDB database.
       Parameters
       ----------
       path : str
         Location of the directory to store the database
       map_size : str, optional
         Maximum size the database may grow to, in MiB. If at any point the
         database grows larger, an exception will be raised and ``setPath`` must
         be called again with a larger ``map_size``. Default is 10(MiB).
       Raises
       ------
       ImportError
         If the Python ``lmdb`` library cannot be loaded
       """
    import lmdb
    # NOTE: If the LMDB database to load is the same as the currently loaded
    # database, we must make sure to close the old ``lmdb.Environment`` first
    if self._path == path: self._impl.close()
    new_impl = lmdb.Environment(path, map_size = map_size * 1048576)
    if self._path != path:
      with new_impl.begin(write = True) as txn:
        for k,v in self.items():
          txn.put(k, v, overwrite=True)
      self._path = path
    self._impl = new_impl
  
  def getPath(self):
    """Return the location of the directory in which this database is stored,
       if this database is implemented as an LMDB database. Return ``None``
       otherwise."""
    return self._path
  
  # Implementation of the methods of the MutableMapping base class
  
  def __len__(self):
    if self._path is None: return len(self._impl)
    with self._impl.begin() as txn: return txn.stat()['entries']
  
  def __getitem__(self, k):
    if self._path is None: return self._impl[k]
    with self._impl.begin() as txn:
      v = txn.get(k)
      if v is None: raise KeyError
      return v
  
  def __setitem__(self, k, v):
    if self._path is None: self._impl[k] = v; return
    with self._impl.begin(write = True) as txn: txn.put(k, v, overwrite=True)
  
  def __delitem__(self, k):
    if self._path is None: del self._impl[k]; return
    with self._impl.begin(write = True) as txn: txn.delete(k)
  
  def _iter(self, fn, keys, values):
    if self._path is None: yield from fn(self._impl); return
    with self._impl.begin() as txn:
      with txn.cursor() as curs:
        yield from curs.iternext(keys, values)
  
  def __iter__(self): yield from self._iter(iter,        True,  False)
  def keys    (self): yield from self._iter(dict.keys,   True,  False)
  def values  (self): yield from self._iter(dict.values, False, True )
  def items   (self): yield from self._iter(dict.items,  True,  True )
  
  # Methods for performing special filters on keys or values
  
  def filterByKeyHexPrefix(self, p_hex):
    """A generator which yields all key-value pairs whose keys have the given
       string as a prefix of their hex representation. If there is a key whose
       hex representation exactly matches the given string, it and its value
       are returned immediately, without whole database being searched."""
    try:
      p = bytes.fromhex(p_hex)
      yield (p, self[p])
    except Exception:
      for k,v in self.items():
        if k.hex().startswith(p_hex):
          yield (k, v)
  
  def filterByMismatchedJSONObjValues(self, obj_ref, delete = False):
    """This generator finds all entries ``k, v`` in the database for which
       ``v``, when deserialized as JSON, does not match ``obj_ref`` - in the
       sense that there is some key in both ``v`` and ``obj_ref`` which has
       differing values in each (see ``mismatchedJSONObjValues``). Each such
       ``k``, paired with ``v``'s list of mismatches (the list returned by
       ``mismatchedJSONObjValues``), is then yielded. If ``delete`` is ``True``,
       each entry is deleted from the database before being yielded."""
    # NOTE: This function could just as well be defined as the body of
    # ``onKVs`` below with ``self.items()`` for ``kvs`` and ``del self[k]``
    # for `deleteFn`. However, that would result in creating an additional
    # LMDB transaction for every deleted element. Instead, we have a special
    # case for LMDB-backed databases which uses only a single tranaction.
    def onKVs(kvs, deleteFn):
      for k,v in kvs:
        try:
          ms = list(mismatchedJSONObjValues(json.loads(v), obj_ref))
          if len(ms) > 0:
            if delete: deleteFn(k)
            yield (k, ms)
        except Exception:
          pass
    if self._path is None:
      yield from onKVs(self._impl.items(), self._impl.__delitem__); return
    with self._impl.begin(write = True) as txn:
      with txn.cursor() as curs:
        yield from onKVs(curs, txn.delete)

# ------------------------------------------------------------------------------
# Helper functions for using LMDBOptDatabase objects with hex strings
# ------------------------------------------------------------------------------

def hex(hex_str):
  """Convert a hex string to ``bytes``"""
  return bytes.fromhex(hex_str)

def jsonHex(obj_hex_str):
  """Convert a hex string to ``bytes`` then deserialize a the result as JSON"""
  return json.loads(hex(obj_hex_str))

def pHex(v):
  """Print the given value as a hex string, if it is a ``bytes`` object"""
  if isinstance(v, bytes): print(v.hex())

def pJSONHex(obj, pretty = False):
  """Serialize the given object as JSON to get a ``bytes`` object then print
     the result as a hex string"""
  print(bytes(json.dumps(obj), 'utf-8').hex())

def pHexPair(v1, v2, pretty = False):
  """Print the given pair of values as a hex strings, if both are ``bytes``
     objects. For the second element, if ``pretty`` is ``True``, deserialise it
     as JSON and print that instead."""
  if isinstance(v1, bytes) and isinstance(v2, bytes):
    print(v1.hex(), json.loads(v2) if pretty else v2.hex())

def pHexJSONPair(v1, obj2, pretty = False):
  """Print the given pair of values as a hex strings, if the first element is a
     ``bytes`` object. For the second element, if ``pretty`` is ``True``, print
     it directly, otherwise serialize it as JSON to get a ``bytes`` object and
     use that to print its hex string."""
  if isinstance(v1, bytes):
    print(v1.hex(), obj2 if pretty else bytes(json.dumps(obj2), 'utf-8').hex())

def pHexPairs(vprs, pretty = False):
  """Print each pair in a given iterable using ``pHexPair``"""
  for v1, v2 in vprs: pHexPair(v1, v2, pretty)

def pHexJSONPairs(vobjprs, pretty = False):
  """Print each pair in a given iterable using ``pHexJSONPair``"""
  for v1, obj2 in vobjprs: pHexJSONPair(v1, obj2, pretty)

# ------------------------------------------------------------------------------
# Interactive Shell Interface
# ------------------------------------------------------------------------------

def main(argv = None):
  if len(argv) > 0 and argv[0] == "shell":
    import code
    code.InteractiveConsole(globals()).interact(banner = '')

if __name__ == '__main__':
    main(sys.argv[1:])
