import os
import os.path
import saw.connection as saw
from saw.proofscript import *

dir_path = os.path.dirname(os.path.realpath(__file__))

c = saw.connect("cabal new-exec --verbose=0 saw-remote-api")

assume_bc = os.path.join(dir_path, 'assume.bc')

c.llvm_load_module('m', assume_bc).result()

seven_contract = {
    "pre vars": [],
    "pre conds": [],
    "pre allocated": [],
    "pre points tos": [],
    "argument vals": [],
    "post vars": [],
    "post conds": [],
    "post allocated": [],
    "post points tos": [],
    "return val": {"setup value": "Cryptol", "expression": "7 : [32]"}
}

addone_contract = {
    "pre vars": [],
    "pre conds": [],
    "pre allocated": [],
    "pre points tos": [],
    "argument vals": [],
    "post vars": [],
    "post conds": [],
    "post allocated": [],
    "post points tos": [],
    "return val": {"setup value": "Cryptol", "expression": "8 : [32]"}
}

prover = ProofScript([abc]).to_json()
c.llvm_assume('m', 'seven', seven_contract, 'seven_ov').result()
c.llvm_verify('m', 'addone', ['seven_ov'], False, addone_contract, prover, 'addone_ov').result()
