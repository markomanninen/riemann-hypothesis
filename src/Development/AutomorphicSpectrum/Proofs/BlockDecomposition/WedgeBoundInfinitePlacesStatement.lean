module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundInfinitePlaces
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub

@[expose] public section

open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wedgeI_of_detMono_mulI_var : DetMono → MulI → WedgeI := by
  first | exact @GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI | exact GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI | (intros; apply GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI <;> assumption)
