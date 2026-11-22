module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

@[expose] public section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_basic_of_conj_places : SzFin → ConjPlaces → SizeBasic := by
  first | exact @GlobalTheory.CompanionTheory.Size.sizeBasic | exact GlobalTheory.CompanionTheory.Size.sizeBasic | (intros; apply GlobalTheory.CompanionTheory.Size.sizeBasic <;> assumption)
