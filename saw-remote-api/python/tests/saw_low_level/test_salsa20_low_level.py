from pathlib import Path
import unittest
import saw_client as saw
from saw_client.llvm import *
from saw_client.proofscript import *




class Salsa20LowLevelTest(unittest.TestCase):
    def test_salsa20(self):
        c = saw.connection.connect(reset_server=True)

        if __name__ == "__main__": saw.view(saw.LogResults())

        bcname = str(Path('tests','saw','test-files', 'salsa20.bc'))
        cryname = str(Path('tests','saw','test-files', 'Salsa20.cry'))

        c.cryptol_load_file(cryname).result()
        c.llvm_load_module('m', bcname).result()

        # SetupVals
        value = {"setup value": "Cryptol", "expression": "value" }
        shift = {"setup value": "Cryptol", "expression": "shift" }
        res = {"setup value": "Cryptol", "expression": "value <<< shift" }

        y0p = {"setup value": "named", "name" : "y0p" }
        y1p = {"setup value": "named", "name" : "y1p" }
        y2p = {"setup value": "named", "name" : "y2p" }
        y3p = {"setup value": "named", "name" : "y3p" }

        y0 = {"setup value": "Cryptol", "expression" : "y0" }
        y1 = {"setup value": "Cryptol", "expression" : "y1" }
        y2 = {"setup value": "Cryptol", "expression" : "y2" }
        y3 = {"setup value": "Cryptol", "expression" : "y3" }

        y0f = {"setup value": "Cryptol", "expression" : "(quarterround [y0, y1, y2, y3]) @ 0" }
        y1f = {"setup value": "Cryptol", "expression" : "(quarterround [y0, y1, y2, y3]) @ 1" }
        y2f = {"setup value": "Cryptol", "expression" : "(quarterround [y0, y1, y2, y3]) @ 2" }
        y3f = {"setup value": "Cryptol", "expression" : "(quarterround [y0, y1, y2, y3]) @ 3" }

        yp = {"setup value": "named", "name" : "yp" }
        y = {"setup value": "Cryptol", "expression" : "y" }

        rr_res = {"setup value": "Cryptol", "expression" : "rowround y" }
        cr_res = {"setup value": "Cryptol", "expression" : "columnround y" }
        dr_res = {"setup value": "Cryptol", "expression" : "doubleround y" }
        hash_res = {"setup value": "Cryptol", "expression" : "Salsa20 y" }
        expand_res = {"setup value": "Cryptol", "expression" : "Salsa20_expansion`{a=2}(k, n)" }
        crypt_res = {"setup value": "Cryptol", "expression" : "Salsa20_encrypt (k, v, m)" }

        rotl_contract = {
            "mutable globals": [],
            "pre vars": [
                {"server name": "value", "name": "value", "type": i32.to_json()},
                {"server name": "shift", "name": "shift", "type": i32.to_json()}
            ],
            "pre conds": ["0 < shift /\\ shift < 32"],
            "pre allocated": [],
            "pre points tos": [],
            "argument vals": [value, shift],
            "post vars": [],
            "post conds": [],
            "post allocated": [],
            "post points tos": [],
            "return val": res
        }

        qr_contract = {
            "mutable globals": [],
            "pre vars": [
                {"server name": "y0", "name": "y0", "type": i32.to_json()},
                {"server name": "y1", "name": "y1", "type": i32.to_json()},
                {"server name": "y2", "name": "y2", "type": i32.to_json()},
                {"server name": "y3", "name": "y3", "type": i32.to_json()}
            ],
            "pre conds": [],
            "pre allocated": [
                {"server name": "y0p",
                "type": i32.to_json(),
                "mutable": True,
                "alignment": None},
                {"server name": "y1p",
                "type": i32.to_json(),
                "mutable": True,
                "alignment": None},
                {"server name": "y2p",
                "type": i32.to_json(),
                "mutable": True,
                "alignment": None},
                {"server name": "y3p",
                "type": i32.to_json(),
                "mutable": True,
                "alignment": None}
            ],
            "pre points tos": [ {"pointer": y0p, "points to": y0},
                                {"pointer": y1p, "points to": y1},
                                {"pointer": y2p, "points to": y2},
                                {"pointer": y3p, "points to": y3} ],
            "argument vals": [y0p, y1p, y2p, y3p],
            "post vars": [],
            "post conds": [],
            "post allocated": [],
            "post points tos": [ {"pointer": y0p, "points to": y0f},
                                {"pointer": y1p, "points to": y1f},
                                {"pointer": y2p, "points to": y2f},
                                {"pointer": y3p, "points to": y3f} ],
            "return val": None
        }

        def oneptr_update_contract(ty, res):
            return {
                "mutable globals": [],
                "pre vars": [
                    {"server name": "y", "name": "y", "type": ty.to_json()}
                ],
                "pre conds": [],
                "pre allocated": [
                    {"server name": "yp",
                    "type": ty.to_json(),
                    "mutable": True,
                    "alignment": None}
                ],
                "pre points tos": [ {"pointer": yp, "points to": y} ],
                "argument vals": [yp],
                "post vars": [],
                "post conds": [],
                "post allocated": [],
                "post points tos": [ {"pointer": yp, "points to": res} ],
                "return val": None
            }

        rr_contract = oneptr_update_contract(LLVMArrayType(i32, 16), rr_res)
        cr_contract = oneptr_update_contract(LLVMArrayType(i32, 16), cr_res)
        dr_contract = oneptr_update_contract(LLVMArrayType(i32, 16), dr_res)
        hash_contract = oneptr_update_contract(LLVMArrayType(i8, 64), hash_res)

        kp = {"setup value": "named", "name" : "kp" }
        np = {"setup value": "named", "name" : "np" }
        ksp = {"setup value": "named", "name" : "ksp" }
        k = {"setup value": "Cryptol", "expression" : "k" }
        n = {"setup value": "Cryptol", "expression" : "n" }
        zero = {"setup value": "Cryptol", "expression" : "0 : [32]" }

        expand_contract = {
            "mutable globals": [],
            "pre vars": [
                {"server name": "k", "name": "k", "type": LLVMArrayType(i8, 32).to_json()},
                {"server name": "n", "name": "n", "type": LLVMArrayType(i8, 16).to_json()}
            ],
            "pre conds": [],
            "pre allocated": [
                {"server name": "kp",
                "type": LLVMArrayType(i8, 32).to_json(),
                "mutable": True,
                "alignment": None},
                {"server name": "np",
                "type": LLVMArrayType(i8, 16).to_json(),
                "mutable": True,
                "alignment": None},
                {"server name": "ksp",
                "type": LLVMArrayType(i8, 64).to_json(),
                "mutable": True,
                "alignment": None}
            ],
            "pre points tos": [ {"pointer": kp, "points to": k},
                                {"pointer": np, "points to": n} ],
            "argument vals": [kp, np, ksp],
            "post vars": [],
            "post conds": [],
            "post allocated": [],
            "post points tos": [ {"pointer": ksp, "points to": expand_res} ],
            "return val": None
        }

        vp = {"setup value": "named", "name" : "vp" }
        mp = {"setup value": "named", "name" : "mp" }
        v = {"setup value": "Cryptol", "expression" : "v" }
        m = {"setup value": "Cryptol", "expression" : "m" }
        def crypt_contract(size : int):
            return {
                "mutable globals": [],
                "pre vars": [
                    {"server name": "k", "name": "k", "type": LLVMArrayType(i8, 32).to_json()},
                    {"server name": "v", "name": "v", "type": LLVMArrayType(i8, 8).to_json()},
                    {"server name": "m", "name": "m", "type": LLVMArrayType(i8, size).to_json()}
                ],
                "pre conds": [],
                "pre allocated": [
                    {"server name": "kp",
                    "type": LLVMArrayType(i8, 32).to_json(),
                    "mutable": True,
                    "alignment": None},
                    {"server name": "vp",
                    "type": LLVMArrayType(i8, 8).to_json(),
                    "mutable": True,
                    "alignment": None},
                    {"server name": "mp",
                    "type": LLVMArrayType(i8, size).to_json(),
                    "mutable": True,
                    "alignment": None}
                ],
                "pre points tos": [ {"pointer": kp, "points to": k},
                                    {"pointer": vp, "points to": v},
                                    {"pointer": mp, "points to": m} ],
                "argument vals": [kp, vp, zero, mp, {"setup value": "Cryptol", "expression": (str(size) + " : [32]")}],
                "post vars": [],
                "post conds": [],
                "post allocated": [],
                "post points tos": [ {"pointer": mp, "points to": crypt_res} ],
                "return val": zero
            }

        prover = ProofScript([z3([])]).to_json()

        c.llvm_verify('m', 'rotl', [], False, rotl_contract, prover, 'rotl_ov').result()
        c.llvm_verify('m', 's20_quarterround', ['rotl_ov'], False, qr_contract, prover, 'qr_ov').result()
        c.llvm_verify('m', 's20_rowround', ['qr_ov'], False, rr_contract, prover, 'rr_ov').result()
        c.llvm_verify('m', 's20_columnround', ['rr_ov'], False, cr_contract, prover, 'cr_ov').result()
        c.llvm_verify('m', 's20_doubleround', ['cr_ov', 'rr_ov'], False, dr_contract, prover, 'dr_ov').result()
        #c.llvm_verify('m', 's20_hash', ['dr_ov'], False, hash_contract, prover, 'hash_ov').result()
        #c.llvm_verify('m', 's20_expand32', ['hash_ov'], False, expand_contract, prover, 'expand_ov').result()
        #c.llvm_verify('m', 's20_crypt32', ['expand_ov'], False, crypt_contract(63), prover, 'crypt_ov').result()

if __name__ == "__main__":
    unittest.main()
