module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformLowerBoundOfSums
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ULowOf

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_lower_bound_of_sums' : _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.HeightCondition → _root_.GlobalTheory.CovTop.CoverHeightSum → _root_.GlobalTheory.CovTop.SumBoundCondition → _root_.GlobalTheory.CovTop.UniformLowerBound := by
  first | exact @_root_.GlobalTheory.CovTop.FromComp.u_low_of_cover_hyps | exact _root_.GlobalTheory.CovTop.FromComp.u_low_of_cover_hyps | (intros; apply _root_.GlobalTheory.CovTop.FromComp.u_low_of_cover_hyps <;> assumption)
end
