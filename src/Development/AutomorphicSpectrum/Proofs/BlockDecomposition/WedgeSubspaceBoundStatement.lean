module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeSubspaceBound
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub

@[expose] public section

open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wedge_subspace_bound : WedgeSub := by
  first | exact @GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub | exact GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub | (intros; apply GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub <;> assumption)
