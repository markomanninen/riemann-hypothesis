module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RadicalSubspaceFacts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

@[expose] public section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radical_subspace_facts : Radical := by
  first | exact @GlobalTheory.CompanionTheory.RadicalForm.radical | exact GlobalTheory.CompanionTheory.RadicalForm.radical | (intros; apply GlobalTheory.CompanionTheory.RadicalForm.radical <;> assumption)
