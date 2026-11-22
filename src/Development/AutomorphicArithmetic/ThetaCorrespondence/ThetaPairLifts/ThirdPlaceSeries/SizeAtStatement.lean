module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeAtHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAtAltAlt

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_at' : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt | exact _root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt <;> assumption)
end
