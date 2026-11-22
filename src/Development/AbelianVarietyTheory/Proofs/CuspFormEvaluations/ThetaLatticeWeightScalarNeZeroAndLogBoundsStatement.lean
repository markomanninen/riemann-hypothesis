module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLatticeWeightScalarNeZeroAndLogBounds
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (w : WeightFamilies.Wt D j), sOf B hinj EX w ≠ 0 ∧ ∀ σ : B.KO →+* ℂ, 0 ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ (WeightAlgebra.DF w : ℝ) / 2 * Real.log (qq D) ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ≤ lamStar D * w.size := by
  first | exact @GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds | exact GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds | (intros; apply GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds <;> assumption)
