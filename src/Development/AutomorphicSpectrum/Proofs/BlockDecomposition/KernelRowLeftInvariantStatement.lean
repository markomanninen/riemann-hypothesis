module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowLeftInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_row_left_invariant : GlobalTheory.CompanionTheory.KerFc.LtSob → GlobalTheory.CompanionTheory.KerFc.LtComm → GlobalTheory.CompanionTheory.KerFc.RowLeft := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.rowLeft | exact GlobalTheory.CompanionTheory.KerFc.rowLeft | (intros; apply GlobalTheory.CompanionTheory.KerFc.rowLeft <;> assumption)
