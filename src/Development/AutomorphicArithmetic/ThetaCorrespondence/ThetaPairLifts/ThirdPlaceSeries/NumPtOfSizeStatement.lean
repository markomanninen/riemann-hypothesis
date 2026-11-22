module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumericalPointOfSize
public import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPtOfSize

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numerical_point_statement_of_size : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.NumPtAlt := by
  first | exact @_root_.GlobalTheory.RefSum.NumSizes.numPt_of_size' | exact _root_.GlobalTheory.RefSum.NumSizes.numPt_of_size' | (intros; apply _root_.GlobalTheory.RefSum.NumSizes.numPt_of_size' <;> assumption)
end
