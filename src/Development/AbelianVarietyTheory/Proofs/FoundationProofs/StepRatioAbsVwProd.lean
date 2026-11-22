module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.ProdFormula

@[expose] public section

open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

namespace GlobalTheory.Square

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem stepRatio_vw_pow (w : Pl K) {x : K} (hx : x ≠ 0) (c : ℕ) : vw w (x ^ c) = c * vw w x := by
  induction c with
  | zero =>
    have h := Formalism.DivisionValues.ValuationRepresentative.vw_mul w (1 : K) 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    rw [pow_zero]
    push_cast
    omega
  | succ c ih =>
    rw [pow_succ, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero c hx) hx, ih]
    push_cast
    ring

theorem stepRatio_vw_of_dvd (w : Pl K) {q c : ℕ} (hq : 0 < q) {g : 𝓞 K} (hg : g ∣ (q : 𝓞 K) ^ c) :
    (g : K) ≠ 0 ∧ 0 ≤ vw w (g : K) ∧ vw w (g : K) ≤ c * vw w (q : K) := by
  obtain ⟨b, hb⟩ := hg
  have hq0 : (q : K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have h : (q : K) ^ c = (g : K) * (b : K) := by
    have := congrArg (fun x : 𝓞 K => (x : K)) hb
    simpa using this
  have hne : (g : K) * (b : K) ≠ 0 := h ▸ pow_ne_zero c hq0
  have hg0 := left_ne_zero_of_mul hne
  have hb0 := right_ne_zero_of_mul hne
  refine ⟨hg0, Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w g, ?_⟩
  rw [← stepRatio_vw_pow w hq0, h, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hg0 hb0]
  have := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w b
  omega

theorem stepRatio_abs_vw_prod (w : Pl K) {T : Type} (S : Finset T) (f : T → K) (r : T → ℝ)
    (h : ∀ v ∈ S, f v ≠ 0 ∧ |(vw w (f v) : ℝ)| ≤ r v) :
    |(vw w (∏ v ∈ S, f v) : ℝ)| ≤ ∑ v ∈ S, r v := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := stepRatio_vw_pow w (one_ne_zero : (1 : K) ≠ 0) 0
    rw [pow_zero, Nat.cast_zero, zero_mul] at this
    rw [Finset.prod_empty, Finset.sum_empty, this]
    simp
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self a S)
    have h2 := fun v hv => h v (Finset.mem_insert_of_mem hv)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h1.1 (Finset.prod_ne_zero_iff.2 fun v hv => (h2 v hv).1)]
    push_cast
    exact (abs_add_le _ _).trans (add_le_add h1.2 (ih h2))

theorem stepRatio_vw_bound : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ₀ : K →+* ℂ) (w : Pl K) (Qn : ℕ),
    (Qn : 𝓞 K) ∉ w.asIdeal → ∀ (T : Type) (S0 : Finset T) (cc qq : T → ℕ), (∀ v ∈ S0, 0 < qq v) → ∀ u1 u0 : ℂ,
    StepRatio σ₀ Qn S0 cc qq u1 u0 → ∃ t : K, t ≠ 0 ∧ u1 = σ₀ t * u0 ∧
      |(vw w t : ℝ)| ≤ 2 * ∑ v ∈ S0, (cc v : ℝ) * (vw w (qq v : K) : ℝ) := by
  intro K _ _ _ σ₀ w Qn hQ T S0 cc qq hq u1 u0 h
  obtain ⟨b, g, g', hb, hg, hu⟩ := h
  have vz : ∀ {a : 𝓞 K}, a ∉ w.asIdeal → vw w (a : K) = 0 := by
    intro a ha
    classical
    have ha0 : (Ideal.span {a} : Ideal (𝓞 K)) ≠ 0 := by
      rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      rintro rfl
      exact ha w.asIdeal.zero_mem
    unfold vw
    rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ ha0]
    by_contra h
    have h' : (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {a})).factors ≠ 0 := by
      intro h0
      exact h (by rw [h0]; rfl)
    exact ha (Ideal.dvd_span_singleton.1 ((Associates.count_ne_zero_iff_dvd ha0 w.irreducible).1 h'))
  have ⟨hb0, hbv⟩ : b ≠ 0 ∧ vw w b = 0 := by
    obtain ⟨a, k, k', ⟨d, hd⟩, he⟩ := hb
    have hpow : ∀ j : ℕ, (Qn : 𝓞 K) ^ j ∉ w.asIdeal :=
      fun j hj => hQ (w.isPrime.mem_of_pow_mem j hj)
    have ha : a ∉ w.asIdeal := fun h => hpow k' (hd ▸ w.asIdeal.mul_mem_right d h)
    have ha0 : (a : K) ≠ 0 := by
      intro h
      have : a = 0 := by exact_mod_cast h
      exact ha (this ▸ w.asIdeal.zero_mem)
    have hb0 : b ≠ 0 := by rintro rfl; rw [zero_mul] at he; exact ha0 he.symm
    have hk0 : (Qn : K) ^ k ≠ 0 := by intro h; rw [h, mul_zero] at he; exact ha0 he.symm
    refine ⟨hb0, ?_⟩
    have h1 := Formalism.DivisionValues.ValuationRepresentative.vw_mul w b _ hb0 hk0
    have h2 := vz ha
    have h3 := vz (hpow k)
    have h4 : ((((Qn : 𝓞 K) ^ k : 𝓞 K)) : K) = (Qn : K) ^ k := by simp
    rw [h4] at h3
    rw [he, h2, h3] at h1
    omega
  have key : ∀ v ∈ S0, (g v : K) / (g' v : K) ≠ 0 ∧
      |(vw w ((g v : K) / (g' v : K)) : ℝ)| ≤ 2 * ((cc v : ℝ) * (vw w (qq v : K) : ℝ)) := by
    intro v hv
    obtain ⟨a0, a1, a2⟩ := stepRatio_vw_of_dvd w (hq v hv) (hg v hv).1
    obtain ⟨b0, b1, b2⟩ := stepRatio_vw_of_dvd w (hq v hv) (hg v hv).2
    refine ⟨div_ne_zero a0 b0, ?_⟩
    rw [div_eq_mul_inv, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ a0 (inv_ne_zero b0), Formalism.DivisionValues.ValuationRepresentative.vw_inv]
    have a1' : (0 : ℝ) ≤ (vw w (g v : K) : ℝ) := by exact_mod_cast a1
    have a2' : (vw w (g v : K) : ℝ) ≤ (cc v : ℝ) * (vw w (qq v : K) : ℝ) := by exact_mod_cast a2
    have b1' : (0 : ℝ) ≤ (vw w (g' v : K) : ℝ) := by exact_mod_cast b1
    have b2' : (vw w (g' v : K) : ℝ) ≤ (cc v : ℝ) * (vw w (qq v : K) : ℝ) := by exact_mod_cast b2
    push_cast
    rw [abs_le]
    constructor <;> linarith
  have hp : ∏ v ∈ S0, (g v : K) / (g' v : K) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v hv => (key v hv).1
  refine ⟨_, mul_ne_zero hb0 hp, hu, ?_⟩
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hb0 hp, hbv, zero_add, Finset.mul_sum]
  exact stepRatio_abs_vw_prod w S0 _ _ key

end GlobalTheory.Square
