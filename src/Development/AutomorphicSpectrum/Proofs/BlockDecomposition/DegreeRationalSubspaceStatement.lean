module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeRationalSubspace
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

@[expose] public section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_rational_subspace : DegBasisG → DegRat := by
  first | exact @GlobalTheory.CompanionTheory.Degree.degRat_of_degBasisG | exact GlobalTheory.CompanionTheory.Degree.degRat_of_degBasisG | (intros; apply GlobalTheory.CompanionTheory.Degree.degRat_of_degBasisG <;> assumption)
