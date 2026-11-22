module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFour
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_four : PositivityTheory.SiegelWeilFormula.Gunr.Q4 := by
  first | exact @GlobalTheory.CompanionTheory.DiscriminantUnit.q4 | exact GlobalTheory.CompanionTheory.DiscriminantUnit.q4 | (intros; apply GlobalTheory.CompanionTheory.DiscriminantUnit.q4 <;> assumption)
