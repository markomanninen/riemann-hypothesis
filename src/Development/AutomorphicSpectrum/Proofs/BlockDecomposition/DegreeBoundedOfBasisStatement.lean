module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBoundedOfBasis
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

@[expose] public section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_bounded_of_basis : WedgeF → WedgeI → MulF → MulI → SzFin → FinSupp → LogAbsBasic → DegBasisG → DegBdd := by
  first | exact @GlobalTheory.CompanionTheory.DegBound.degBdd_of | exact GlobalTheory.CompanionTheory.DegBound.degBdd_of | (intros; apply GlobalTheory.CompanionTheory.DegBound.degBdd_of <;> assumption)
