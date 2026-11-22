module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePartIdentity
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpaTie

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leafHeightMapBound_of_infK : _root_.GlobalTheory.BigTop.Fun.BundleCondition → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → InfK → _root_.GlobalTheory.BigTop.Fun.LeafHeightMapBound @Comparison₂ := by
  first | exact @_root_.GlobalTheory.QuotientNormCoisometry.leafHeightMapBound_tie_of_infK | exact _root_.GlobalTheory.QuotientNormCoisometry.leafHeightMapBound_tie_of_infK | (intros; apply _root_.GlobalTheory.QuotientNormCoisometry.leafHeightMapBound_tie_of_infK <;> assumption)
end
