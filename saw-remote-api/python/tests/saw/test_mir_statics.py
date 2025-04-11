import unittest
from pathlib import Path

from saw_client import *
from saw_client.crucible import cry, cry_f, global_var, global_initializer
from saw_client.mir import Contract, u32


class F1Contract(Contract):
    def specification(self) -> None:
        self.execute_func()

        self.returns(global_initializer('mir_statics::S1'))


class F1AltContract(Contract):
    def specification(self) -> None:
        s1_static = global_var('mir_statics::S1')
        init = cry_f('42 : [32]')
        self.points_to(s1_static, init)

        self.execute_func()

        self.points_to(s1_static, init)
        self.returns(init)


class F2Contract(Contract):
    def specification(self) -> None:
        self.execute_func()

        self.returns(global_var('mir_statics::S2'))


class F3Contract(Contract):
    def specification(self) -> None:
        s3_static = global_var('mir_statics::S3')
        self.points_to(s3_static, global_initializer('mir_statics::S3'))

        self.execute_func()

        ret = cry_f('4 : [32]')
        self.points_to(s3_static, ret)
        self.returns(ret)


class F3AltContract(Contract):
    def specification(self) -> None:
        s3_static = global_var('mir_statics::S3')
        init = cry_f('42 : [32]')
        self.points_to(s3_static, init)

        self.execute_func()

        ret = cry_f('{init} + 1 : [32]')
        self.points_to(s3_static, ret)
        self.returns(ret)


class GContract(Contract):
    def specification(self) -> None:
        r_ref = self.alloc(u32, read_only = True)

        self.execute_func(r_ref)

        self.returns(cry_f('False'))


class GAltContract(Contract):
    def specification(self) -> None:
        self.execute_func(global_var('mir_statics::S1'))

        self.returns(cry_f('True'))


class MIRStaticsTest(unittest.TestCase):
    def test_mir_statics(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        json_name = str(Path('tests', 'saw', 'test-files', 'mir_statics.linked-mir.json'))
        mod = mir_load_module(json_name)

        f1_result = mir_verify(mod, 'mir_statics::f1', F1Contract())
        self.assertIs(f1_result.is_success(), True)

        f1_alt_result = mir_verify(mod, 'mir_statics::f1', F1AltContract())
        self.assertIs(f1_alt_result.is_success(), True)

        f2_result = mir_verify(mod, 'mir_statics::f2', F2Contract())
        self.assertIs(f2_result.is_success(), True)

        f3_result = mir_verify(mod, 'mir_statics::f3', F3Contract())
        self.assertIs(f3_result.is_success(), True)

        f3_alt_result = mir_verify(mod, 'mir_statics::f3', F3AltContract())
        self.assertIs(f3_alt_result.is_success(), True)

        g_result = mir_verify(mod, 'mir_statics::g', GContract())
        self.assertIs(g_result.is_success(), True)

        g_alt_result = mir_verify(mod, 'mir_statics::g', GAltContract())
        self.assertIs(g_alt_result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
