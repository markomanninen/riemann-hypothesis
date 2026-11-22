module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLaurentSeriesSumCongruentModPPow
public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_laurentSeries_sum_congruent_mod_p_pow :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
      (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ →
    ∀ (d : ℕ) (e : Fin d → Ω) (b : Fin d → O0 p), (∀ t, IsInt (p := p) (e t)) →
    ∀ K : ℕ, ∃ a : Fin d → Lau p,
      Cong (p := p) K (∑ t, e t * ψ (b t))
        (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) := by
  intro p hp Ω _ _ T n ψ h d e b he K
  have hq : IsIntegral (O0 p) (T.qq n) := by
    refine ⟨Polynomial.X ^ (p ^ n) - Polynomial.C (qO p),
      Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero), ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
      GlobalTheory.K5.Basic.qq_pow, sub_self]
  have hψ (x : O0 p) : IsIntegral (O0 p) (ψ x) := by
    have hx : ψ x ∈ ψ.range := ⟨x, rfl⟩
    rw [h.rng] at hx
    exact adjoin_le_integralClosure hq hx
  choose a c hac using fun t => GlobalTheory.GeoFix.exists_lau_approx p K (b t)
  refine ⟨a, ∑ t, e t * ψ (c t), IsIntegral.sum _ fun t _ => (he t).mul (hψ (c t)), ?_⟩
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hac t, map_add (f := ψ), map_mul, map_pow, map_natCast]
  ring
