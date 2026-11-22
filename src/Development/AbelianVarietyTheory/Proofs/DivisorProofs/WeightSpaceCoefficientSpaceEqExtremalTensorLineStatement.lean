module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSpaceCoefficientSpaceEqExtremalTensorLine
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalD
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualWeylHighestWeightSpaceLineField

@[expose] public section

set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightSpace_coefficientSpace_eq_extremalTensorLine : ∀ (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n), (∀ m ∈ (ten fun τ => extremal K n (lam τ) : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) ∧ ∀ G ∈ VV K lam, (∀ m ∈ G.support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) → ∃ c : K, G = c • ten fun τ => extremal K n (lam τ) := by
  first | exact @GlobalTheory.CoefWtLine.weight_line | exact GlobalTheory.CoefWtLine.weight_line | (intros; apply GlobalTheory.CoefWtLine.weight_line <;> assumption)
