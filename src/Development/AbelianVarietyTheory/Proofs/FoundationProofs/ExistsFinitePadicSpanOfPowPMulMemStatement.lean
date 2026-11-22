module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePadicSpanOfPowPMulMem
public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_padic_span_of_pow_p_mul_mem :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
      IsClo p Ω → ∀ (d : ℕ) (E : Fin d → Ω),
        (∀ t, IsInt (p := p) (E t) ∧ IsAlgZp (p := p) (E t)) →
        ∀ v : ℕ, ∃ (m : ℕ) (f : Fin m → Ω),
          (∀ j, IsInt (p := p) (f j) ∧ IsAlgZp (p := p) (f j)) ∧
          ∀ (l : Fin d → ℤ_[p]) (y : Ω), IsInt (p := p) y →
            (p : Ω) ^ v * y = ∑ t, zp Ω (l t) * E t →
            ∃ μ : Fin m → ℤ_[p], y = ∑ j, zp Ω (μ j) * f j := by
  intro p _ Ω _ _ hc d E hE v
  let : Algebra ℤ_[p] Ω := zpAlg (p := p) (Ω := Ω)
  have : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  have hAlg (x : Ω) : IsAlgZp (p := p) x ↔ IsAlgebraic ℤ_[p] x := by
    unfold IsAlgZp IsAlgebraic
    simp only [Polynomial.aeval_map_algebraMap]
  have hsmul (c : ℤ_[p]) (x : Ω) : c • x = zp Ω c * x := by
    rw [Algebra.smul_def]
    congr 1
    change algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) c) = zp Ω c
    rw [zp, algebraMap_zp_eq, HahnSeries.C_apply]
  have hpv : ((p : Ω) ^ v) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  let S : Submodule ℤ_[p] Ω := Submodule.span ℤ_[p] (Set.range E)
  let S' : Submodule ℤ_[p] Ω :=
    { carrier := {y | IsInt (p := p) y ∧ (p : Ω) ^ v * y ∈ S}
      add_mem' := by
        rintro x y ⟨hxInt, hxS⟩ ⟨hyInt, hyS⟩
        exact ⟨IsIntegral.add hxInt hyInt, by rw [mul_add]; exact S.add_mem hxS hyS⟩
      zero_mem' := ⟨isIntegral_zero, by simp⟩
      smul_mem' := by
        rintro c x ⟨hxInt, hxS⟩
        refine ⟨?_, ?_⟩
        · change IsIntegral (O0 p) (c • x)
          rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[p] (O0 p) Ω]
          exact IsIntegral.mul isIntegral_algebraMap hxInt
        · change (p : Ω) ^ v * (c • x) ∈ S
          rw [mul_smul_comm]
          exact S.smul_mem c hxS }
  let U := Submodule.span ℤ_[p] (Set.range fun t => E t / (p : Ω) ^ v)
  have hle : S' ≤ U := by
    rintro y ⟨_, hy⟩
    change (p : Ω) ^ v * y ∈ Submodule.span ℤ_[p] (Set.range E) at hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hy
    apply (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).2
    refine ⟨c, ?_⟩
    calc
      ∑ t, c t • (E t / (p : Ω) ^ v) = (∑ t, c t • E t) / (p : Ω) ^ v := by
        simp only [Finset.sum_div, smul_div_assoc]
      _ = y := (div_eq_iff hpv).2 (hc.trans (mul_comm _ _))
  have hnoeth : IsNoetherian ℤ_[p] U :=
    isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))
  have hfg : S'.FG := isNoetherian_submodule.1 hnoeth S' hle
  obtain ⟨m, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hfmem (j : Fin m) : IsInt (p := p) (f j) ∧ (p : Ω) ^ v * f j ∈ S := by
    change f j ∈ S'
    rw [← hf]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hAlgS : ∀ x ∈ S, IsAlgebraic ℤ_[p] x := by
    intro x hx
    change x ∈ Submodule.span ℤ_[p] (Set.range E) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact (hAlg _).1 (hE t).2
    | zero => exact isAlgebraic_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx =>
      rw [Algebra.smul_def]
      exact (isAlgebraic_algebraMap c).mul hx
  refine ⟨m, f, fun j => ⟨(hfmem j).1, ?_⟩, ?_⟩
  · apply (hAlg _).2
    have hInv : IsAlgebraic ℤ_[p] (((p : Ω) ^ v)⁻¹) :=
      ((isAlgebraic_natCast p : IsAlgebraic ℤ_[p] (p : Ω)).pow v).inv
    have h := hInv.mul (hAlgS _ (hfmem j).2)
    rwa [← mul_assoc, inv_mul_cancel₀ hpv, one_mul] at h
  · intro l y hy hyl
    have hyS : y ∈ S' := by
      refine ⟨hy, ?_⟩
      rw [hyl]
      refine S.sum_mem fun t _ => ?_
      rw [← hsmul]
      exact S.smul_mem _ (Submodule.subset_span ⟨t, rfl⟩)
    rw [← hf] at hyS
    obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hyS
    exact ⟨μ, by simpa only [hsmul] using hμ.symm⟩
