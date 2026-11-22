module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairFiniteDimensional
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

@[expose] public section

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_finite_dimensional : GlobalTheory.CompanionTheory.EGlue.PairFD := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.pairFD_holds | exact GlobalTheory.CompanionTheory.EGlue.pairFD_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.pairFD_holds <;> assumption)
