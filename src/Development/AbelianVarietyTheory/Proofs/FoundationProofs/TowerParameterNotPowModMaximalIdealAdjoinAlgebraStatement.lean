module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerParameterNotPowModMaximalIdealAdjoinAlgebra
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerParameter_not_pow_mod_maximalIdeal_adjoin_algebraic : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgZp (p := p) s) →
  ∀ y ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)), IsInt (p := p) y →
    ¬ ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω)) := by
  intro p _ Ω _ _ hclo S hS y hy hyint
  rintro ⟨m, hm, hmint⟩
  classical
  have := Basic.charZero_of_isClo hclo
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have huni := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
  have hmax : (Ideal.span {(p : O0 p)}).IsMaximal := by
    rw [← huni]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [huni]
    exact GlobalTheory.T.unramified_integers_adic_complete p
  have := hclo.alg
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_valuation_le_one_iff_isIntegral_of_complete_dvr
    (O0 p) Ω hclo.inj
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hvp0 : 0 < v (p : Ω) := (Valuation.pos_iff v).2 hp0
  have hvp1 : v (p : Ω) < 1 := by
    have hpint : IsIntegral (O0 p) (p : Ω) := by
      simpa only [map_natCast] using
        (isIntegral_algebraMap (A := Ω) (x := (p : O0 p)))
    refine lt_of_le_of_ne ((hv _).2 hpint) ?_
    intro heq
    have hinv : IsInt (p := p) ((p : Ω)⁻¹) := (hv _).1 (by rw [map_inv₀, heq, inv_one])
    exact Basic.not_cong_one_zero hclo 1 one_ne_zero
      ⟨(p : Ω)⁻¹, hinv, by rw [sub_zero, pow_one, mul_inv_cancel₀ hp0]⟩
  let : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra
  have : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap ℤ_[p] Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    have e := PadicInt.unitCoeff_spec hx0
    rw [e, map_mul, map_pow, map_natCast] at hx
    rcases mul_eq_zero.1 hx with h | h
    · exact ((Units.isUnit _).map (algebraMap ℤ_[p] Ω)).ne_zero h
    · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h
  have hvint : ∀ x : Ω, IsIntegral ℤ_[p] x → v x ≤ 1 := fun x hx =>
    (hv x).2 (IsIntegral.tower_top (A := O0 p) hx)
  have hSalg : ∀ s ∈ S, IsAlgebraic ℤ_[p] s := by
    intro s hs
    obtain ⟨P, hP0, hP⟩ := hS s hs
    exact ⟨P, hP0, by rwa [Polynomial.aeval_map_algebraMap] at hP⟩
  obtain ⟨R, hRfin, hRpid, hRS⟩ := GlobalTheory.T.exists_finite_pid_subalgebra_padicInt_contains_fractions p Ω hinj S hSalg
  obtain ⟨π, hπR, hπ0, hvπ, hpπ, f, hf, hstep⟩ :=
    GlobalTheory.T.exists_uniformizer_valuation_lt_one_frobenius_congr p Ω hinj v hvint hvp1 R hRfin hRpid
  have hfg : (Subalgebra.toSubmodule R).FG := Module.Finite.iff_fg.1 hRfin
  obtain ⟨T, hT⟩ := Subalgebra.fg_of_fg_toSubmodule hfg
  have hRB : ∀ x ∈ R, x ∈ Algebra.adjoin (O0 p) (T : Set Ω) := by
    intro x hx
    have hle : Algebra.adjoin ℤ_[p] (T : Set Ω) ≤
        (Algebra.adjoin (O0 p) (T : Set Ω)).restrictScalars ℤ_[p] :=
      Algebra.adjoin_le (fun t ht => (Subalgebra.mem_restrictScalars _).2 (Algebra.subset_adjoin ht))
    rw [hT] at hle
    exact (Subalgebra.mem_restrictScalars _).1 (hle hx)
  have hTR : ∀ t ∈ T, t ∈ R := fun t ht => hT ▸ Algebra.subset_adjoin (Finset.mem_coe.2 ht)
  have hTint : ∀ t ∈ T, IsIntegral (O0 p) t := fun t ht =>
    (IsIntegral.of_mem_of_fg R hfg t (hTR t ht)).tower_top
  obtain ⟨hdiv, hres⟩ := GlobalTheory.K5.NotPow.residue_core p (O0 p) Ω hmax v hv T hTint π (hRB _ hπR) hπ0 hvπ
    (hRB _ hpπ) f hf (fun t ht => hRB _ (hstep t (hTR t ht)))
  have hBint : ∀ x ∈ Algebra.adjoin (O0 p) (T : Set Ω), v x ≤ 1 := fun x hx =>
    (hv x).2 (Algebra.adjoin_le (S := integralClosure (O0 p) Ω) (fun t ht => hTint t ht) hx)
  have hclosed := GlobalTheory.T.div_mem_subalgebra_of_valuation_le_one_of_uniformizer (O0 p) Ω v hv _ hBint π (hRB _ hπR) hπ0 hvπ hdiv
  have hsub : Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)) ≤
      Subfield.closure (Algebra.adjoin (O0 p) (T : Set Ω) : Set Ω) := by
    rw [Subfield.closure_le]
    rintro x (⟨c, rfl⟩ | hx)
    · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ c)
    · obtain ⟨a, ha, b, hb, rfl⟩ := hRS x hx
      exact div_mem (Subfield.subset_closure (hRB _ ha)) (Subfield.subset_closure (hRB _ hb))
  obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.1 (hsub hy)
  have hcl : ∀ z ∈ Subring.closure (Algebra.adjoin (O0 p) (T : Set Ω) : Set Ω),
      z ∈ Algebra.adjoin (O0 p) (T : Set Ω) := fun z hz =>
    (Subring.closure_le (t := (Algebra.adjoin (O0 p) (T : Set Ω)).toSubring)).2 (fun _ h => h) hz
  have hyv : v y ≤ 1 := (hv y).2 hyint
  have hyB : y ∈ Algebra.adjoin (O0 p) (T : Set Ω) := by
    rw [← hab]
    exact hclosed a (hcl a ha) b (hcl b hb) (by rw [hab]; exact hyv)
  have hvq : v (y ^ p - algebraMap (O0 p) Ω (qO p)) < 1 := by
    have h1 := (hv _).2 hmint
    rw [map_div₀, map_pow] at h1
    have h2 : v (y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m < 1 :=
      lt_of_le_of_lt ((div_le_one₀ hvp0).1 h1) hvp1
    by_contra hc
    push Not at hc
    exact absurd h2 (not_lt.2 (one_le_pow₀ hc))
  obtain ⟨b, hb⟩ := hres y hyB (qO p) hvq
  have hbv : v (algebraMap (O0 p) Ω b) ≤ 1 := (hv _).2 isIntegral_algebraMap
  have hvb : v (algebraMap (O0 p) Ω (b ^ p - qO p)) < 1 := by
    have e : algebraMap (O0 p) Ω (b ^ p - qO p) = (y ^ p - algebraMap (O0 p) Ω (qO p)) -
        (y ^ p - (algebraMap (O0 p) Ω b) ^ p) := by
      rw [map_sub, map_pow]
      ring
    have hg : v (y ^ p - (algebraMap (O0 p) Ω b) ^ p) < 1 := by
      rw [← geom_sum₂_mul, map_mul]
      have hs : v (∑ i ∈ Finset.range p, y ^ i * (algebraMap (O0 p) Ω b) ^ (p - 1 - i)) ≤ 1 := by
        apply v.map_sum_le
        intro i _
        rw [map_mul, map_pow, map_pow]
        exact mul_le_one' (pow_le_one' hyv _) (pow_le_one' hbv _)
      calc _ ≤ 1 * v (y - algebraMap (O0 p) Ω b) := mul_le_mul_of_nonneg_right hs zero_le
        _ < 1 := by rw [one_mul]; exact hb
    rw [e]
    exact lt_of_le_of_lt (v.map_sub _ _) (max_lt hvq hg)
  have hdvd : (p : O0 p) ∣ b ^ p - qO p := by
    by_contra hnd
    have hu : IsUnit (b ^ p - qO p) := by
      by_contra hnu
      apply hnd
      have hmem : b ^ p - qO p ∈ IsLocalRing.maximalIdeal (O0 p) :=
        (IsLocalRing.mem_maximalIdeal _).2 hnu
      rw [huni] at hmem
      exact Ideal.mem_span_singleton.1 hmem
    obtain ⟨u, hu⟩ := hu
    have h1 : v (algebraMap (O0 p) Ω (u : O0 p)) * v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have h2 : v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) ≤ 1 := (hv _).2 isIntegral_algebraMap
    rw [← hu] at hvb
    have h4 : v (algebraMap (O0 p) Ω (u : O0 p)) * v (algebraMap (O0 p) Ω (↑u⁻¹ : O0 p)) < 1 :=
      calc _ ≤ v (algebraMap (O0 p) Ω (u : O0 p)) * 1 := mul_le_mul_of_nonneg_left h2 zero_le
        _ < 1 := by rw [mul_one]; exact hvb
    rw [h1] at h4
    exact lt_irrefl _ h4
  exact GlobalTheory.K5.NotPow.q_not_pow_mod p b hdvd
