module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupOperatorDepthMulDisjointColumns
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.RootStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.FactorialWeightedSumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.OmBStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame

@[expose] public section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupOperatorDepth_mul_disjoint_columns : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (S : Set κ) (P Q : MvPolynomial (Σ b, ι b) C), (∀ x ∈ P.vars, x.1 ∈ S) → (∀ x ∈ Q.vars, x.1 ∉ S) → depth G u (P * Q) = depth G u P + depth G u Q := by
  first | exact @GlobalTheory.FGDepth.depth_mul_of_disjoint_columns | exact GlobalTheory.FGDepth.depth_mul_of_disjoint_columns | (intros; apply GlobalTheory.FGDepth.depth_mul_of_disjoint_columns <;> assumption)
