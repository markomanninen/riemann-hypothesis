module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPointOfWeightNumerical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumericalPointOfSize
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPointOfSize
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefTheta
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumPtOfSize

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_pt_of_size : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.SumPtAlt := by
  first | exact @_root_.GlobalTheory.RefSum.sumPt_of_size_alt | exact _root_.GlobalTheory.RefSum.sumPt_of_size_alt | (intros; apply _root_.GlobalTheory.RefSum.sumPt_of_size_alt <;> assumption)
end
