module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapFirstProperty
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_map_first_property : PositivityTheory.Rg.Tf.Loc.N1 := by
  first | exact @GlobalTheory.CompanionTheory.NormOnto.norm_onto | exact GlobalTheory.CompanionTheory.NormOnto.norm_onto | (intros; apply GlobalTheory.CompanionTheory.NormOnto.norm_onto <;> assumption)
