module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundFinitePlaces
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub

@[expose] public section

open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wedge_bound_finite_places : MulF → WedgeF := by
  first | exact @GlobalTheory.CompanionTheory.Wedge.wedgeF_of_mulF | exact GlobalTheory.CompanionTheory.Wedge.wedgeF_of_mulF | (intros; apply GlobalTheory.CompanionTheory.Wedge.wedgeF_of_mulF <;> assumption)
