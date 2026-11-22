module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationSubringPullbackIntegralElements
public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationSubring_pullback_integral_elements :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime]
      (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl,
      ∃ B : ValuationSubring Ω, ((p : ℕ) : Ω) ∈ B.nonunits ∧
        ∀ x, x ∈ B ↔ IsInt (p := p) (j x) := by
  intro Ω _ _ _ p _ Ωl _ _ hC j
  have existsValuation : ∃ v : Valuation Ωl NNReal,
      (∀ x : Ωl, v x ≤ 1 ↔ IsInt (p := p) x) ∧ v (p : Ωl) < 1 := by
    obtain ⟨_, hdvr, hp⟩ := GlobalTheory.T.completed_laurent_isDVR_statement p
    have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
      rw [hp.maximalIdeal_eq]
      exact GlobalTheory.T.unramified_integers_adic_complete p
    have := hC.alg
    obtain ⟨v, hv⟩ := GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr
      (O0 p) Ωl hC.inj
    refine ⟨v, hv, ?_⟩
    have : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hC
    have hp0 : (p : Ωl) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hle : v (p : Ωl) ≤ 1 := (hv _).2 (by
      have := GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ωl) (p : ℤ)
      simpa [IsInt] using this)
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hi : v (p : Ωl)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
    exact GlobalTheory.K5.Basic.not_cong_one_zero hC 1 one_ne_zero
      ⟨(p : Ωl)⁻¹, (hv _).1 hi, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩
  obtain ⟨v, hv, hp⟩ := existsValuation
  let w := v.comap j
  refine ⟨w.valuationSubring, ?_, fun x => ?_⟩
  · rw [ValuationSubring.mem_nonunits_iff, ← map_one w.valuationSubring.valuation,
      ← w.isEquiv_valuation_valuationSubring.lt_iff_lt, map_one]
    change v (j (p : Ω)) < 1
    rw [map_natCast]
    exact hp
  · rw [Valuation.mem_valuationSubring_iff]
    exact hv (j x)
