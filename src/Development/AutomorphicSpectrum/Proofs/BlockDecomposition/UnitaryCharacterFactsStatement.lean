module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryCharacterFacts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan

@[expose] public section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_character_facts : PositivityTheory.SphericalProduct.CharU := by
  first | exact @GlobalTheory.CompanionTheory.TorusChar.charU | exact GlobalTheory.CompanionTheory.TorusChar.charU | (intros; apply GlobalTheory.CompanionTheory.TorusChar.charU <;> assumption)
