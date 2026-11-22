module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankTwoDefiniteUnimodularHermitianClassBound
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_two_definite_unimodular_hermitian_class_bound : RankTwoClasses := by
  first | exact @GlobalTheory.RankTwoCount.rankTwoClasses | exact GlobalTheory.RankTwoCount.rankTwoClasses | (intros; apply GlobalTheory.RankTwoCount.rankTwoClasses <;> assumption)
