module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyIsotropicSubspaces
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

@[expose] public section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.only_isotropic_subspaces : OnlyStable → DegPairing → SizeBasic → OnlyIsotropic := by
  first | exact @GlobalTheory.CompanionTheory.IsotropicDegreeBound.onlyIsotropic_of | exact GlobalTheory.CompanionTheory.IsotropicDegreeBound.onlyIsotropic_of | (intros; apply GlobalTheory.CompanionTheory.IsotropicDegreeBound.onlyIsotropic_of <;> assumption)
