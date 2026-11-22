module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerPadicDeterminantFormula
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pAdicFrobeniusStickelberger_of_d7_datum : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicFrobeniusStickelberger D := by
  first | exact @GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula | exact GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula | (intros; apply GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula <;> assumption)
