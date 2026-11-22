module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAltBis

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cov_size_bound : _root_.GlobalTheory.CovTop.SizeCondition := by
  first | exact @_root_.GlobalTheory.CovTop.SizeRows.size_alt_bis | exact _root_.GlobalTheory.CovTop.SizeRows.size_alt_bis | (intros; apply _root_.GlobalTheory.CovTop.SizeRows.size_alt_bis <;> assumption)
end
