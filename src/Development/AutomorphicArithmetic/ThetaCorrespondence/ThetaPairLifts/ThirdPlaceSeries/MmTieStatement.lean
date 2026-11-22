module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityAtFittedPoints
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MmTie

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leafMinimalMass_of_setAt : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → _root_.GlobalTheory.BigTop.Fun.LeafMinimalMass @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie_alt | exact _root_.GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.LeafMMTie.mm_tie_alt <;> assumption)
end
