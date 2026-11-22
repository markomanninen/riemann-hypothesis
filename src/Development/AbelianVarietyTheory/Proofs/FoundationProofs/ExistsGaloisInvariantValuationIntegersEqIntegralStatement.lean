module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
public import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisInvariant_valuation_integers_eq_integral :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
      IsClo p Ω → ∃ v : Valuation Ω ℝ≥0,
        (∀ x : Ω, v x ≤ 1 ↔ GlobalTheory.K5.IsInt (p := p) x) ∧
        (∀ (g : Gal p Ω) (x : Ω), v (g x) = v x) ∧ 0 < v (p : Ω) ∧ v (p : Ω) < 1 := by
  intro p _ Ω _ _ h
  obtain ⟨_, hdvr, hirr⟩ := GlobalTheory.T.completed_laurent_isDVR_statement p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    hirr.maximalIdeal_eq
  have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [hmax]
    exact GlobalTheory.T.unramified_integers_adic_complete p
  have := h.alg
  have hvaluation :=
    GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr (O0 p) Ω h.inj
  obtain ⟨v, hv⟩ := hvaluation
  have hinv := GlobalTheory.T.valuation_algEquiv_apply_eq_of_le_one_iff_isIntegral (O0 p) Ω h.inj v hv
  have : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨v, hv, hinv, (Valuation.pos_iff v).2 hp0, ?_⟩
  have hle : v (p : Ω) ≤ 1 := (hv _).2 (by
    have := GlobalTheory.K5.Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
    simpa [GlobalTheory.K5.IsInt] using this)
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hi : v (p : Ω)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
  have hint : GlobalTheory.K5.IsInt (p := p) ((p : Ω)⁻¹) := (hv _).1 hi
  exact GlobalTheory.K5.Basic.not_cong_one_zero h 1 one_ne_zero
    ⟨(p : Ω)⁻¹, hint, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩
