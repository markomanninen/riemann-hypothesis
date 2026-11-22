module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

@[expose] public section

open scoped Matrix

noncomputable section

open MeasureTheory Complex
open scoped Real RealInnerProductSpace ComplexConjugate FourierTransform SchwartzMap

namespace GlobalTheory.RealWeil.SchurSchwartz

variable {l : Type} [Fintype l]

def modPt (q : EuclideanSpace ℝ l) : l ⊕ l → ℝ := Sum.elim 0 fun i => q i

def trPt (p : EuclideanSpace ℝ l) : l ⊕ l → ℝ := Sum.elim (fun i => p i) 0

theorem pPart_modPt (q : EuclideanSpace ℝ l) : pPart (modPt q) = 0 := by
  ext i; simp [pPart, modPt]

theorem qPart_modPt (q : EuclideanSpace ℝ l) : qPart (modPt q) = q := by
  ext i; simp [qPart, modPt]

theorem pPart_trPt (p : EuclideanSpace ℝ l) : pPart (trPt p) = p := by
  ext i; simp [pPart, trPt]

theorem qPart_trPt (p : EuclideanSpace ℝ l) : qPart (trPt p) = 0 := by
  ext i; simp [qPart, trPt]

theorem rhoFun_modPt (q : EuclideanSpace ℝ l) (f : EuclideanSpace ℝ l → ℂ) (x : EuclideanSpace ℝ l) :
    rhoFun (modPt q) f x = cexp (((2 * π * ⟪q, x⟫ : ℝ) : ℂ) * I) * f x := by
  simp [rhoFun, phase, pPart_modPt, qPart_modPt]

theorem rhoFun_trPt (p : EuclideanSpace ℝ l) (f : EuclideanSpace ℝ l → ℂ) (x : EuclideanSpace ℝ l) :
    rhoFun (trPt p) f x = f (x + p) := by
  simp [rhoFun, phase, pPart_trPt, qPart_trPt]

def modS (q : EuclideanSpace ℝ l) (g : Sch l) : Sch l :=
  SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ l => GlobalTheory.Published.Metaplectic.eChar ⟪q, x⟫) g

theorem coe_modS (q : EuclideanSpace ℝ l) (g : Sch l) : ⇑(modS q g) = rhoFun (modPt q) ⇑g := by
  have ht : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => GlobalTheory.Published.Metaplectic.eChar ⟪q, x⟫ :=
    GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (innerSL ℝ q).hasTemperateGrowth
  funext x
  rw [modS, SchwartzMap.smulLeftCLM_apply_apply ht, GlobalTheory.Published.Metaplectic.eChar_apply, rhoFun_modPt, smul_eq_mul]
  congr 2
  push_cast
  ring

def trS (p : EuclideanSpace ℝ l) (g : Sch l) : Sch l := SchwartzMap.compSubConstCLM ℂ (-p) g

theorem coe_trS (p : EuclideanSpace ℝ l) (g : Sch l) : ⇑(trS p g) = rhoFun (trPt p) ⇑g := by
  funext x
  rw [trS, SchwartzMap.compSubConstCLM_apply, rhoFun_trPt, sub_neg_eq_add]

theorem integrable_conj_mul (a b : Sch l) : Integrable (fun x => conj (a x) * b x) := by
  refine b.integrable.bdd_mul (c := SchwartzMap.seminorm ℝ 0 0 a)
    (Complex.continuous_conj.comp a.continuous).aestronglyMeasurable (.of_forall fun x => ?_)
  rw [Complex.norm_conj]
  exact SchwartzMap.norm_le_seminorm ℝ a x

theorem integral_conj_mul_eq (U : Sch l →ₗ[ℂ] Sch l)
    (hU : ∀ h : Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) (f g : Sch l) :
    ∫ x, conj (U f x) * U g x = ∫ x, conj (f x) * g x := by
  have hn : ∀ h : Sch l, ‖(U h).toLp 2‖ = ‖h.toLp 2‖ := fun h => by
    rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) (U h).continuous.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) h.continuous.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, hU]
  have hlin : ∀ (b : ℂ) (u v : Sch l), u.toLp 2 volume + b • v.toLp 2 volume = (u + b • v).toLp 2 volume := fun b u v => by
    have := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l))).map_add u (b • v)
    rw [(SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l))).map_smul] at this
    exact this.symm
  have key : ∀ b : ℂ, ‖(U f).toLp 2 volume + b • (U g).toLp 2 volume‖ = ‖f.toLp 2 volume + b • g.toLp 2 volume‖ := fun b => by
    rw [hlin, hlin, ← map_smul, ← map_add (f := _), hn]
  have k1 := key 1
  have k2 := key (-1)
  have k3 := key (-(RCLike.I : ℂ))
  have k4 := key (RCLike.I : ℂ)
  simp only [one_smul, neg_one_smul, neg_smul, ← sub_eq_add_neg] at k1 k2 k3 k4
  have e1 := SchwartzMap.inner_toL2_toL2_eq (U f) (U g) volume
  have e2 := SchwartzMap.inner_toL2_toL2_eq f g volume
  simp only [RCLike.inner_apply] at e1 e2
  simp only [mul_comm (starRingEnd ℂ _)]
  rw [← e1, ← e2, inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, k1, k2, k3, k4]

end GlobalTheory.RealWeil.SchurSchwartz

namespace GlobalTheory.RealWeil.SchurSchwartz

variable {l : Type} [Fintype l]

theorem conj_mul_eq (U : Sch l →ₗ[ℂ] Sch l)
    (hc : ∀ (w : l ⊕ l → ℝ) (h h₁ : Sch l), ⇑h₁ = rhoFun w ⇑h → ⇑(U h₁) = rhoFun w ⇑(U h))
    (hU : ∀ h : Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) (f g : Sch l) (x : EuclideanSpace ℝ l) :
    conj (U f x) * U g x = conj (f x) * g x := by
  set D : EuclideanSpace ℝ l → ℂ := fun y => conj (U f y) * U g y - conj (f y) * g y with hD
  have hDi : Integrable D := (integrable_conj_mul (U f) (U g)).sub (integrable_conj_mul f g)
  have hDc : Continuous D :=
    ((Complex.continuous_conj.comp (U f).continuous).mul (U g).continuous).sub
      ((Complex.continuous_conj.comp f.continuous).mul g.continuous)
  have hF : 𝓕 D = 0 := by
    funext w
    rw [Real.fourier_eq', Pi.zero_apply]
    have h1 := hc (modPt (-w)) g (modS (-w) g) (coe_modS _ _)
    have h2 := integral_conj_mul_eq U hU f (modS (-w) g)
    rw [← sub_eq_zero, ← integral_sub (integrable_conj_mul _ _) (integrable_conj_mul _ _)] at h2
    rw [← h2]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [h1, coe_modS, rhoFun_modPt, hD, smul_eq_mul]
    rw [inner_neg_left, real_inner_comm]
    push_cast
    ring_nf
  have hinv := hDc.fourierInv_fourier_eq hDi (by rw [hF]; exact integrable_zero _ _ _)
  have hz : 𝓕⁻ (0 : EuclideanSpace ℝ l → ℂ) = 0 := by
    first
      | exact FourierTransform.fourierInv_zero
      | (funext w; simp [Real.fourierInv_eq])
  rw [hF, hz] at hinv
  have hx := congrFun hinv x
  simp only [hD, Pi.zero_apply] at hx
  exact sub_eq_zero.1 hx.symm

end GlobalTheory.RealWeil.SchurSchwartz

end
