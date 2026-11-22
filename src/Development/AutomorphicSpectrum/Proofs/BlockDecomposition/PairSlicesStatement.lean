module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSlices
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

@[expose] public section

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_slices : GlobalTheory.CompanionTheory.EGlue.PairSlices := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.pairSlices | exact GlobalTheory.CompanionTheory.EGlue.pairSlices | (intros; apply GlobalTheory.CompanionTheory.EGlue.pairSlices <;> assumption)
