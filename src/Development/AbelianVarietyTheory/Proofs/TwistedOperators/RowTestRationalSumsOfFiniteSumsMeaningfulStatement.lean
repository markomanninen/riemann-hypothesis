module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRationalSumsOfFiniteSumsMeaningful
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTestRationalSums_of_finiteSumsMeaningful : GlobalTheory.RowClaim.SumOKK → GlobalTheory.RowClaim.SumRatK := by
  first | exact @GlobalTheory.RowTest.sumRatK_of_sumOKK | exact GlobalTheory.RowTest.sumRatK_of_sumOKK | (intros; apply GlobalTheory.RowTest.sumRatK_of_sumOKK <;> assumption)
