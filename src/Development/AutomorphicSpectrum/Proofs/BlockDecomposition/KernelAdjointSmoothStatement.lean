module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelAdjointSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_adjoint_smooth : GlobalTheory.CompanionTheory.KerFc.AdjSmooth := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.adjSmooth | exact GlobalTheory.CompanionTheory.KerFc.adjSmooth | (intros; apply GlobalTheory.CompanionTheory.KerFc.adjSmooth <;> assumption)
