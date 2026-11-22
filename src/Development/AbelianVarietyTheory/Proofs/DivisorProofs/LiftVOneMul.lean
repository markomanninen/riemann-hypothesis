module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertAvgDual

section Local

variable {F : Type} [Field F] [NumberField F]

theorem eq_of_tens_eq {κ : Type} [Fintype κ] (v : Pl (F := F)) {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0)
    (hRv : ∀ x z, At (evFin F v) z → R (x + z) = R x) {φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (h : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext t
  have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hat : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hR : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by simpa using hRv 0 _ hat
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hR] at e
  exact mul_right_cancel₀ hR0 e

theorem acts_one {κ : Type} [Fintype κ] (v : Pl (F := F)) (φ : (κ → Fv F v) → ℂ) :
    Acts (evFin F v) (1 : Module.End ℂ ((κ → AF F) → ℂ)) φ φ := fun _ _ => rfl

theorem acts_comp {κ : Type} [Fintype κ] (v : Pl (F := F)) (T S : Module.End ℂ ((κ → AF F) → ℂ))
    (hT : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) S φ₁ φ₂) : Acts (evFin F v) (S * T) φ φ₂ := by
  intro r hr
  have e := h₁ r hr
  have hr' : Rest (evFin F v) φ₁ r := ⟨hr.1, e ▸ hT _ hr.2⟩
  rw [Module.End.mul_apply, e]
  exact h₂ r hr'

end Local

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Stab

end GlobalTheory.InertAvgDual
