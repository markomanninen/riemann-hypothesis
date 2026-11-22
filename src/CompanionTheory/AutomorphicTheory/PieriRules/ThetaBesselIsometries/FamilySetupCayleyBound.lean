module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevEAddTwo
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelSumNormSqLeStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyEndomorphismsModularStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselCayleySideBoundStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupBesselGrowthStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.QuotientMeasureAeMemAndMeasurableBesselModelStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.NumericalFamilyShapeGaps
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.RatioMoment

theorem iterate_bound {X M ι : Type} [MeasurableSpace X] [NormedAddCommGroup M] [Fintype ι] (μ : Measure X)
    (κ : X → ℝ) (f : M → X → ℝ) (T : ι → ι → M → M) (L : ℕ → M → Prop) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hκ : AEMeasurable κ μ) (hf : ∀ w, AEMeasurable (f w) μ) (hf0 : ∀ w x, 0 ≤ f w x)
    (hpt : ∀ᵐ x ∂μ, ∀ w, κ x ^ 2 * f w x ≤ ∑ c, ∑ e, f (T c e w) x)
    (hL : ∀ j w, L j w → ∀ c e, L (j + 2) (T c e w))
    (hs : ∀ j w, j ≤ N → L j w → ∑ c, ∑ e, ‖T c e w‖ ^ 2 ≤ B ^ 2 * ‖w‖ ^ 2)
    (h0 : ∀ w, ∫⁻ x, ENNReal.ofReal (1 * f w x) ∂μ ≤ ENNReal.ofReal (‖w‖ ^ 2)) :
    ∀ q j, j + 2 * q ≤ N → ∀ w, L j w →
      ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * q) * f w x) ∂μ ≤ ENNReal.ofReal (B ^ (2 * q) * ‖w‖ ^ 2) := by
  intro q
  induction q with
  | zero => intro j _ w _; simpa using h0 w
  | succ q ih =>
    intro j hj w hw
    have hk0 : ∀ x, 0 ≤ κ x ^ (2 * q) := fun x => (even_two_mul q).pow_nonneg _
    have hm : ∀ v, AEMeasurable (fun x => ENNReal.ofReal (κ x ^ (2 * q) * f v x)) μ := fun v =>
      ((hκ.pow_const _).mul (hf v)).ennreal_ofReal
    calc ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * (q + 1)) * f w x) ∂μ
        ≤ ∫⁻ x, ∑ c, ∑ e, ENNReal.ofReal (κ x ^ (2 * q) * f (T c e w) x) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpt] with x hx
          have h1 : κ x ^ (2 * (q + 1)) * f w x ≤ ∑ c, ∑ e, κ x ^ (2 * q) * f (T c e w) x := by
            simp only [← Finset.mul_sum, mul_add_one, pow_add, mul_assoc]
            exact mul_le_mul_of_nonneg_left (hx w) (hk0 x)
          refine (ENNReal.ofReal_le_ofReal h1).trans_eq ?_
          rw [ENNReal.ofReal_sum_of_nonneg fun c _ =>
            Finset.sum_nonneg fun e _ => mul_nonneg (hk0 x) (hf0 _ x)]
          exact Finset.sum_congr rfl fun c _ =>
            ENNReal.ofReal_sum_of_nonneg fun e _ => mul_nonneg (hk0 x) (hf0 _ x)
      _ = ∑ c, ∑ e, ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * q) * f (T c e w) x) ∂μ := by
          rw [lintegral_finsetSum' _ fun c _ => Finset.aemeasurable_fun_sum _ fun e _ => hm _]
          exact Finset.sum_congr rfl fun c _ => lintegral_finsetSum' _ fun e _ => hm _
      _ ≤ ∑ c, ∑ e, ENNReal.ofReal (B ^ (2 * q) * ‖T c e w‖ ^ 2) := by
          gcongr with c _ e _
          exact ih (j + 2) (by omega) _ (hL j w hw c e)
      _ = ENNReal.ofReal (∑ c, ∑ e, B ^ (2 * q) * ‖T c e w‖ ^ 2) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun c _ => Finset.sum_nonneg fun e _ => by positivity]
          exact Finset.sum_congr rfl fun c _ => (ENNReal.ofReal_sum_of_nonneg fun e _ => by positivity).symm
      _ ≤ ENNReal.ofReal (B ^ (2 * (q + 1)) * ‖w‖ ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := mul_le_mul_of_nonneg_left (hs j w (by omega) hw) (pow_nonneg hB (2 * q))
          simp only [Finset.mul_sum] at this
          exact this.trans_eq (by ring)

theorem ratio_moment : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν ≤ q0 → ∀ (j q : ℕ), j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ (a : Fin r) (w : (R ν).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc) ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ 2) ^ (2 * q) * ‖w‖ ^ 2) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν j q hjq a w hw
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hmass := (Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν).1
  obtain ⟨hNum, hFam, hG, hSF⟩ := hS
  have hDG := hFam ν hν
  obtain ⟨hBe, hdg, -⟩ := hSF ν hν
  obtain ⟨hae, -, hlen, hl⟩ := Gp91.GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDG hG
  have hMod := Gp91.GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hNum.1 hDG Q (E ν) hQ (hE ν hν).1
  obtain ⟨⟨hbv, -⟩, hsh⟩ := _root_.GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  refine iterate_bound νq
    (fun x => lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc)
    (fun (v : (R ν).smSub) x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) (fun c e v => E ν c e v)
    (Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)))
    (4 * (2 * r + k + 1) ^ 2) (b ^ 2) (by positivity) ((hlen _).div (hlen _))
    (fun v => (((hl (l ν) hBe.1 v v.2).norm.aemeasurable).pow_const 2).const_mul _)
    (fun v x => by positivity) ?_
    (fun i v hv c e => _root_.GlobalTheory.lev_E_add_two _ _ _ _ _ i v hMod.1 hMod.2.1 hv c e)
    (fun i v hi hv => ?_) (fun v => hmass v v.2) q j hjq w hw
  · filter_upwards [hae] with x hx v
    have h1 := mul_le_mul_of_nonneg_left
      (Gp91.GlobalTheory.T.bessel_cayley_side_bound hK k r _ _ (R ν) Wp z π u μW μN μG νq (l ν) Q (E ν) hDG hG hBe.1 hQ
        (hE ν hν).1 _ hx a v) hdg.le
    simp only [Finset.mul_sum] at h1
    linarith
  · have h1 := _root_.GlobalTheory.T.unitaryGlModule_level_sum_norm_sq_le _ _ _ _ _ k i bv b v hMod (hsh ν hν).2.1 hbv hi hv
    linarith [show (b ^ 2) ^ 2 = b ^ 4 by ring]

end GlobalTheory.RatioMoment
