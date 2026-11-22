module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSecondProperty
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_second_property : PositivityTheory.Rg.Tf.Loc.D0a → PositivityTheory.Rg.Tf.Loc.L2 := by
  first | exact @GlobalTheory.CompanionTheory.Tf.Loc.stableLattice_unitIntegral | exact GlobalTheory.CompanionTheory.Tf.Loc.stableLattice_unitIntegral | (intros; apply GlobalTheory.CompanionTheory.Tf.Loc.stableLattice_unitIntegral <;> assumption)
