module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceShift
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

@[expose] public section

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_shift : GlobalTheory.CompanionTheory.EGlue.ConvShift := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.convShift_holds | exact GlobalTheory.CompanionTheory.EGlue.convShift_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.convShift_holds <;> assumption)
