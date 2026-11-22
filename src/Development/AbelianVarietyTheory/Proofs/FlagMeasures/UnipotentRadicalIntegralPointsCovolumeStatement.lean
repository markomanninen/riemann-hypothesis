module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalIntegralPointsCovolume
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_integral_points_covolume : RadicalCovolume := by
  first | exact @GlobalTheory.RadCov.radicalCovolume | exact GlobalTheory.RadCov.radicalCovolume | (intros; apply GlobalTheory.RadCov.radicalCovolume <;> assumption)
