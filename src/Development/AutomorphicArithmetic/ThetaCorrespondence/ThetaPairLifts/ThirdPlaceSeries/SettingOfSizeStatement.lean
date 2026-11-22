module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetAtOfSizeAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingOfSize

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.set_at_of_size_at' : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt | exact _root_.GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.setAt_of_sizeAt_alt <;> assumption)
end
