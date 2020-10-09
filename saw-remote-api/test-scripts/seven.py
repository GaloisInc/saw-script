import os
import os.path
import saw.connection as saw
from saw.proofscript import *
from env_server import *

dir_path = os.path.dirname(os.path.realpath(__file__))

c = env_connect()

seven_bc = os.path.join(dir_path, 'seven.bc')

c.llvm_load_module('m', seven_bc).result()

contract = {
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

prover = ProofScript([abc]).to_json()
print(c.llvm_verify('m', 'seven', [], False, contract, prover, 'ok').result())
