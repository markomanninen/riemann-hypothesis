module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueTowerPowersLinearIndependent
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

@[expose] public section

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_tower_powers_linearIndependent : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ E : Subfield Ω, Set.range (algebraMap (O0 p) Ω) ⊆ (E : Set Ω) →
  (∀ y ∈ E, IsInt (p := p) y →
    ¬ ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((y ^ p - algebraMap (O0 p) Ω (qO p)) ^ m / (p : Ω))) →
  ∀ (T : Tower p Ω) (N : ℕ) (d : ℕ → Ω), (∀ j < p ^ N, d j ∈ E ∧ IsInt (p := p) (d j)) →
  (∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j) ^ m / (p : Ω))) →
  ∀ j < p ^ N, ∃ m : ℕ, 0 < m ∧ IsInt (p := p) (d j ^ m / (p : Ω)) := by
  intro p hp Ω _ _ h E hE hq T N d hd hs
  classical
  have := Basic.charZero_of_isClo h
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have mem_rad_iff (x : integralClosure (O0 p) Ω) :
      x ∈ (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical ↔
        ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((x : Ω) ^ m / (p : Ω)) := by
    constructor
    · rintro ⟨n, hn⟩
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hn
      refine ⟨n + 1, n.succ_pos, ?_⟩
      have h1 : (z : Ω) * p = (x : Ω) ^ n := by exact_mod_cast congrArg Subtype.val hz
      have h2 : (x : Ω) ^ (n + 1) / p = ((z * x : integralClosure (O0 p) Ω) : Ω) := by
        rw [pow_succ, ← h1]; push_cast; field_simp
      rw [h2]
      exact (z * x).2
    · rintro ⟨m, -, hm⟩
      refine ⟨m, Ideal.mem_span_singleton'.2 ⟨⟨_, hm⟩, Subtype.ext ?_⟩⟩
      push_cast
      field_simp
  have isInt_inv (x : Ω) (hx0 : x ≠ 0)
      (hx : ¬ ∃ m : ℕ, 0 < m ∧ IsInt (p := p) (x ^ m / (p : Ω))) :
      IsInt (p := p) x⁻¹ := by
    obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
    have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
    have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) :=
      hmax ▸ o0_isAdicComplete_span_p p
    have : FaithfulSMul (O0 p) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 h.inj
    let : Algebra (FractionRing (O0 p)) Ω := FractionRing.liftAlgebra (O0 p) Ω
    have : IsScalarTower (O0 p) (FractionRing (O0 p)) Ω :=
      FractionRing.isScalarTower_liftAlgebra (O0 p) Ω
    have : Algebra.IsAlgebraic (O0 p) Ω := h.alg
    have : Algebra.IsAlgebraic (FractionRing (O0 p)) Ω :=
      Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
    obtain ⟨a, b, hb, h1, h2⟩ :=
      exists_pow_div_zpow_isIntegral (O0 p) (FractionRing (O0 p)) Ω (p : O0 p) hirr x hx0
    rw [map_natCast] at h1 h2
    have hpi : IsIntegral (O0 p) (p : Ω) := by
      exact_mod_cast Basic.isInt_intCast (p := p) (Ω := Ω) (p : ℤ)
    by_cases ha : 0 < a
    · exfalso
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = (n + 1 : ℕ) := ⟨(a - 1).toNat, by push_cast; omega⟩
      refine hx ⟨b, hb, ?_⟩
      have : x ^ b / (p : Ω) = x ^ b / (p : Ω) ^ ((n + 1 : ℕ) : ℤ) * (p : Ω) ^ n := by
        rw [zpow_natCast]; field_simp; ring
      rw [this]
      exact h1.mul (hpi.pow n)
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -(n : ℤ) := ⟨(-a).toNat, by omega⟩
      refine IsIntegral.of_pow hb ?_
      have : x⁻¹ ^ b = (p : Ω) ^ (-(n : ℤ)) / x ^ b * (p : Ω) ^ n := by
        rw [zpow_neg, zpow_natCast, inv_pow]; field_simp
      rw [this]
      exact h2.mul (hpi.pow n)
  set M := (Ideal.span {(p : integralClosure (O0 p) Ω)}).radical with hM
  have hmem : ∀ x : integralClosure (O0 p) Ω, Ideal.Quotient.mk M x = 0 ↔
      ∃ m : ℕ, 0 < m ∧ IsInt (p := p) ((x : Ω) ^ m / (p : Ω)) := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, hM, mem_rad_iff]
  have : M.IsMaximal := ResidueIndep.rad_isMaximal h
  let : Field (integralClosure (O0 p) Ω ⧸ M) := Ideal.Quotient.field M
  have : CharP (integralClosure (O0 p) Ω ⧸ M) p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (Ideal.Quotient.mk M),
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.le_radical (Ideal.mem_span_singleton_self _)
  let K : Subfield (integralClosure (O0 p) Ω ⧸ M) :=
    { (E.toSubring.comap (integralClosure (O0 p) Ω).val.toRingHom).map (Ideal.Quotient.mk M) with
      inv_mem' := by
        rintro _ ⟨y, hy, rfl⟩
        by_cases h0 : Ideal.Quotient.mk M y = 0
        · exact ⟨0, E.zero_mem, by rw [h0, inv_zero, map_zero]⟩
        · have h1 : (y : Ω) ≠ 0 := by
            intro hy0
            have : y = 0 := Subtype.ext hy0
            exact h0 (by rw [this, map_zero])
          have h2 := isInt_inv (y : Ω) h1 (fun hh => h0 ((hmem y).2 hh))
          refine ⟨⟨_, h2⟩, E.inv_mem hy, ?_⟩
          refine eq_inv_of_mul_eq_one_left ?_
          rw [← map_mul, ← map_one (Ideal.Quotient.mk M)]
          congr 1
          exact Subtype.ext (inv_mul_cancel₀ h1) }
  have hqi : IsIntegral (O0 p) (T.qq N) :=
    IsIntegral.of_pow (pow_pos hp.out.pos N) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  let t : integralClosure (O0 p) Ω := ⟨_, hqi⟩
  have ht : ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) = algebraMap (O0 p) Ω (qO p) := by
    rw [← Basic.qq_pow T N]; rfl
  let d' : ℕ → integralClosure (O0 p) Ω := fun j => if hj : j < p ^ N then ⟨d j, (hd j hj).2⟩ else 0
  have hd' : ∀ j < p ^ N, (d' j : Ω) = d j := fun j hj => by simp only [d', dite_eq_left hj]
  have key := ResidueIndep.field_indep p K N (Ideal.Quotient.mk M t)
    ⟨t ^ p ^ N, by
      show ((t ^ p ^ N : integralClosure (O0 p) Ω) : Ω) ∈ E
      rw [ht]; exact hE ⟨_, rfl⟩, map_pow _ _ _⟩
    (by
      rintro _ ⟨y, hy, rfl⟩ hb
      refine hq y hy y.2 ?_
      rw [← ht]
      have hz : Ideal.Quotient.mk M (y ^ p - t ^ p ^ N) = 0 := by
        rw [RingHom.map_sub, RingHom.map_pow, RingHom.map_pow, hb, sub_self]
      have := (hmem (y ^ p - t ^ p ^ N)).1 hz
      exact this)
    (fun j => Ideal.Quotient.mk M (d' j))
    (fun j hj => ⟨d' j, by
      show (d' j : Ω) ∈ E
      rw [hd' j hj]; exact (hd j hj).1, rfl⟩)
    (by
      have e : ((∑ j ∈ Finset.range (p ^ N), d' j * t ^ j : integralClosure (O0 p) Ω) : Ω) =
          ∑ j ∈ Finset.range (p ^ N), d j * T.qq N ^ j := by
        push_cast
        exact Finset.sum_congr rfl fun j hj => by rw [hd' j (Finset.mem_range.1 hj)]
      have := (hmem _).2 (e ▸ hs)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sum, map_mul, map_pow] using this)
  intro j hj
  rw [← hd' j hj]
  exact (hmem _).1 (key j hj)
