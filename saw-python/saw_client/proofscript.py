from abc import ABCMeta, abstractmethod
from typing import Any, List

class Prover(metaclass=ABCMeta):
  @abstractmethod
  def to_json(self) -> Any: pass

class ABC(Prover):
  def to_json(self) -> Any:
    return { "name": "abc" }

class ABC_Verilog(Prover):
  def to_json(self) -> Any:
    return { "name": "w4-abc-verilog" }

class ABC_SMTLib(Prover):
  def to_json(self) -> Any:
    return { "name": "w4-abc-smtlib" }

class ABC_SBV(Prover):
  def to_json(self) -> Any:
    return { "name": "sbv-abc" }

class Boolector(Prover):
  def to_json(self) -> Any:
    return { "name": "boolector" }

class Boolector_SBV(Prover):
  def to_json(self) -> Any:
    return { "name": "sbv-boolector" }

class RME(Prover):
  def to_json(self) -> Any:
    return { "name": "rme" }

class UnintProver(Prover):
  def __init__(self, name : str, unints : List[str]) -> None:
    self.name = name
    self.unints = unints

  def to_json(self) -> Any:
    return { "name": self.name, "uninterpreted functions": self.unints }

class Bitwuzla(UnintProver):
  def __init__(self, unints : List[str]) -> None:
    super().__init__("w4-bitwuzla", unints)

class CVC5(UnintProver):
  def __init__(self, unints : List[str]) -> None:
    super().__init__("w4-cvc5", unints)

class Yices(UnintProver):
  def __init__(self, unints : List[str]) -> None:
    super().__init__("w4-yices", unints)

class Z3(UnintProver):
  def __init__(self, unints : List[str]) -> None:
    super().__init__("w4-z3", unints)

class Bitwuzla_SBV(UnintProver):
  def __init__(self, unints : List[str]) -> None:
    super().__init__("sbv-bitwuzla", unints)

class CVC5_SBV(UnintProver):
  def __init__(self, unints : List[str]) -> None:
    super().__init__("sbv-cvc5", unints)

class Yices_SBV(UnintProver):
  def __init__(self, unints : List[str]) -> None:
    super().__init__("sbv-yices", unints)

class Z3_SBV(UnintProver):
  def __init__(self, unints : List[str]) -> None:
    super().__init__("sbv-z3", unints)

class ProofTactic(metaclass=ABCMeta):
  @abstractmethod
  def to_json(self) -> Any: pass

class UseProver(ProofTactic):
  def __init__(self, prover : Prover) -> None:
    self.prover = prover

  def to_json(self) -> Any:
    return { "tactic": "use prover",
             "prover": self.prover.to_json() }

class Unfold(ProofTactic):
  def __init__(self, names : List[str]) -> None:
    self.names = names

  def to_json(self) -> Any:
    return { "tactic": "unfold", "names": self.names }

class EvaluateGoal(ProofTactic):
  def __init__(self, names : List[str]) -> None:
    self.names = names

  def to_json(self) -> Any:
    return { "tactic": "evaluate goal", "names": self.names }

# TODO: add "simplify"

class Admit(ProofTactic):
  def to_json(self) -> Any:
    return { "tactic": "admit" }

class BetaReduceGoal(ProofTactic):
  def to_json(self) -> Any:
    return { "tactic": "beta reduce goal" }

class Trivial(ProofTactic):
  def to_json(self) -> Any:
    return { "tactic": "trivial" }

class Quickcheck(ProofTactic):
  def __init__(self, num_inputs : int) -> None:
    self.num_inputs = num_inputs

  def to_json(self) -> Any:
    return { "tactic": "quickcheck",
             "number of inputs": self.num_inputs }

class ProofScript:
  def __init__(self, tactics : List[ProofTactic]) -> None:
    self.tactics = tactics

  def to_json(self) -> Any:
    return { 'tactics': [t.to_json() for t in self.tactics] }

abc = UseProver(ABC())
abc_smtlib = UseProver(ABC_SMTLib())
abc_verilog = UseProver(ABC_Verilog())
rme = UseProver(RME())
boolector = UseProver(Boolector())

def bitwuzla(unints : List[str]) -> ProofTactic:
  return UseProver(Bitwuzla(unints))

def cvc5(unints : List[str]) -> ProofTactic:
  return UseProver(CVC5(unints))

def yices(unints : List[str]) -> ProofTactic:
  return UseProver(Yices(unints))

def z3(unints : List[str]) -> ProofTactic:
  return UseProver(Z3(unints))
