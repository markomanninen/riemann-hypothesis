module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterExistsUnique
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistedIndependenceLemma.TwistedIndependence

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_character_exists_unique : PositivityTheory.Lbc.HeckeExistsUnique := by
  first | exact @GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique | exact GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique | (intros; apply GlobalTheory.CompanionTheory.HeckeFixed.heckeExistsUnique <;> assumption)
