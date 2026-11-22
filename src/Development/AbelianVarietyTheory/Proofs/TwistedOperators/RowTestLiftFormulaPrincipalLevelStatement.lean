module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestLiftFormulaPrincipalLevel
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel

@[expose] public section

open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTestLiftFormula_principalLevel : StepProj → StepFlip → StepUnfold → StepJets → ConstK → SumOKK → Formula2K := by
  first | exact @GlobalTheory.RowClaim.FormulaTwo.formula2K | exact GlobalTheory.RowClaim.FormulaTwo.formula2K | (intros; apply GlobalTheory.RowClaim.FormulaTwo.formula2K <;> assumption)
