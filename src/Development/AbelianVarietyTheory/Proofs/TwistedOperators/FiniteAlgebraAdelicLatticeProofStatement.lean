module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAlgebraAdelicLatticeProof
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAlgebraAdelicLattice_proof : GlobalTheory.RegSS.TensorLattice := by
  first | exact @GlobalTheory.RegSSLattice.tensorLattice | exact GlobalTheory.RegSSLattice.tensorLattice | (intros; apply GlobalTheory.RegSSLattice.tensorLattice <;> assumption)
