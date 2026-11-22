module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps

@[expose] public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace GlobalTheory.HeckeFamilyMatrices

def ev (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) : SL(2, ℤ) → ℂ := fun x => (F ∣[k] x) τ

section EtaSix

open Complex Function ModularForm
open scoped Manifold Real

def eta6 (z : ℍ) : ℂ := ModularForm.eta z ^ 6

lemma eta_six_ne_zero (z : ℍ) : eta6 z ≠ 0 := pow_ne_zero _ (eta_ne_zero z.2)

lemma eta_six_product_formula (z : ℍ) : eta6 z = Periodic.qParam 4 z * (∏' n, (1 - eta_q n z)) ^ 6 := by
  simp only [eta6, ModularForm.eta, mul_pow]
  congr
  simp [Periodic.qParam, ← Complex.exp_nsmul, nsmul_eq_mul]
  congr 1
  ring

lemma eta6_slash_three_T_eq_I_smul : eta6 ∣[(3 : ℤ)] ModularGroup.T = (Complex.I : ℂ) • eta6 := by
  ext z
  rw [SL_slash_apply, ModularGroup.denom_apply, modular_T_smul]
  have h1 : ∀ n, eta_q n (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = eta_q n z := by
    intro n
    simp only [eta_q, Periodic.qParam, coe_vadd]
    rw [← exp_periodic (2 * π * Complex.I * z / ((1:ℝ):ℂ))]
    congr 2
    push_cast; ring
  have h2 : Periodic.qParam 4 (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = Complex.I * Periodic.qParam 4 z := by
    simp only [Periodic.qParam, coe_vadd]
    rw [← exp_pi_div_two_mul_I, ← Complex.exp_add, exp_pi_div_two_mul_I]
    congr 1
    push_cast; ring
  simp only [eta_six_product_formula, h1, h2, Pi.smul_apply, smul_eq_mul]
  simp [ModularGroup.T, mul_assoc]

lemma sqrt_pow_six (z : ℂ) : Complex.sqrt z ^ 6 = z ^ 3 := by
  have : Complex.sqrt z ^ 2 = z := by
    simp [Complex.sqrt]
  rw [show 6 = 2 * 3 by rfl, pow_mul, this]

lemma eta_six_slash_S : eta6 ∣[(3 : ℤ)] ModularGroup.S = (Complex.I : ℂ) • eta6 := by
  ext z
  rw [SL_slash_apply, UpperHalfPlane.modular_S_smul, ModularGroup.denom_S]
  have he : η (-(↑z)⁻¹) = (Complex.sqrt Complex.I)⁻¹ * (Complex.sqrt z * η z) := by
    simpa [neg_div] using eta_comp_eq_csqrt_I_inv z.2
  have hz := z.ne_zero
  simp only [eta6, inv_neg, he, mul_pow, inv_pow, sqrt_pow_six, Pi.smul_apply, smul_eq_mul]
  have : (Complex.I : ℂ) ^ 3 = -Complex.I := by rw [pow_succ, I_sq]; ring
  rw [this, zpow_neg, inv_neg, inv_I]
  field_simp

lemma eta_six_slash_root_of_unity (γ : SL(2, ℤ)) : ∃ c : ℂ, c ^ 4 = 1 ∧ eta6 ∣[(3 : ℤ)] γ = c • eta6 := by
  have hγ : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨Complex.I, I_pow_four, eta_six_slash_S⟩
    · exact ⟨Complex.I, I_pow_four, eta6_slash_three_T_eq_I_smul⟩
  | one => exact ⟨1, by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, by rw [mul_pow, ha, hb, one_mul], ?_⟩
    rw [SlashAction.slash_mul, hx, SL_smul_slash, hy, smul_smul]
  | inv x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    refine ⟨a⁻¹, by rw [inv_pow, ha, inv_one], ?_⟩
    have : eta6 = a • eta6 ∣[(3 : ℤ)] x⁻¹ := by
      rw [← SL_smul_slash, ← hx, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
    conv_rhs => rw [this]
    rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]

def eta6MultiplierFunction (γ : SL(2, ℤ)) : ℂ := (eta6 ∣[(3 : ℤ)] γ) UpperHalfPlane.I / eta6 UpperHalfPlane.I

lemma eta6Mult0_eq {γ : SL(2, ℤ)} {c : ℂ} (h : eta6 ∣[(3 : ℤ)] γ = c • eta6) : eta6MultiplierFunction γ = c := by
  simp [eta6MultiplierFunction, h, eta_six_ne_zero]

lemma eta_six_slash_multiplier (γ : SL(2, ℤ)) : eta6 ∣[(3 : ℤ)] γ = eta6MultiplierFunction γ • eta6 := by
  obtain ⟨c, -, h⟩ := eta_six_slash_root_of_unity γ
  rw [eta6Mult0_eq h, h]

def eta6Mult : SL(2, ℤ) →* ℂ where
  toFun := eta6MultiplierFunction
  map_one' := eta6Mult0_eq (by simp)
  map_mul' x y := eta6Mult0_eq (by
    rw [SlashAction.slash_mul, eta_six_slash_multiplier, SL_smul_slash, eta_six_slash_multiplier, smul_smul])

lemma eta6Mult_T_eq_I : eta6Mult ModularGroup.T = Complex.I := eta6Mult0_eq eta6_slash_three_T_eq_I_smul

lemma eta6Mult_S : eta6Mult ModularGroup.S = Complex.I := eta6Mult0_eq eta_six_slash_S

lemma eta6Mult_neg_one : eta6Mult (-1) = -1 := by
  have : (-1 : SL(2, ℤ)) = ModularGroup.S * ModularGroup.S := by decide
  rw [this, map_mul, eta6Mult_S, I_mul_I]

def eta6Group : Subgroup SL(2, ℤ) := eta6Mult.toHomUnits.ker

lemma mem_eta6Group (γ : SL(2, ℤ)) : γ ∈ eta6Group ↔ eta6Mult γ = 1 := by
  simp [eta6Group, MonoidHom.mem_ker, Units.ext_iff]

lemma neg_one_not_mem_eta6Group : (-1 : SL(2, ℤ)) ∉ eta6Group := by
  rw [mem_eta6Group, eta6Mult_neg_one]; norm_num

end EtaSix

end GlobalTheory.HeckeFamilyMatrices
