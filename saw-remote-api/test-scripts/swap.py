import os
import os.path
import saw.connection as saw
from saw.proofscript import *
from env_server import *

dir_path = os.path.dirname(os.path.realpath(__file__))

c = env_connect()

swap_bc = os.path.join(dir_path, 'swap.bc')

c.llvm_load_module('m', swap_bc).result()

i32 = {"type": "primitive type", "primitive": "integer", "size": 32}

# ServerNames
xp_name = {"name": "xp"}
yp_name = {"name": "yp"}

# SetupVals
xp = {"setup value": "saved", "name": "xp"}
yp = {"setup value": "saved", "name": "yp"}
x = {"setup value": "Cryptol", "expression": "x" }
y = {"setup value": "Cryptol", "expression": "x" }

contract = {
    "pre vars": [
        {"server name": "x", "name": "x", "type": i32},
        {"server name": "y", "name": "y", "type": i32}
    ],
    "pre conds": [],
    "pre allocated": [
        {"server name": "xp",
         "type": i32,
         "mutable": True,
         "alignment": None},
        {"server name": "yp",
         "type": i32,
         "mutable": True,
         "alignment": None}
    ],
    "pre points tos": [{"pointer": xp, "points to": x},
                       {"pointer": yp, "points to": y}],
    "argument vals": [xp, yp],
    "post vars": [],
    "post conds": [],
    "post allocated": [],
    "post points tos": [{"pointer": xp, "points to": y},
                        {"pointer": yp, "points to": x}],
    "return val": None
}

prover = ProofScript([abc]).to_json()
print(c.llvm_verify('m', 'swap', [], False, contract, prover, 'ok').result())
