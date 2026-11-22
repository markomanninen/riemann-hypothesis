module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumExhaustionUnramified
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_exhaustion_unramified : PositivityTheory.SiegelWeilFormula.Gunr.TsumExhaust := by
  first | exact @GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop | exact GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop | (intros; apply GlobalTheory.CompanionTheory.Exhaustion.tsum_exhaust_prop <;> assumption)
