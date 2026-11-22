module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueLinearDisjointnessCoeffLtOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral

@[expose] public section

open scoped MatrixGroups NNReal
open Polynomial GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_linear_disjointness_coeff_lt_one :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
      IsClo p Ω → ∀ (v : Valuation Ω ℝ≥0), (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) →
      v (p : Ω) < 1 → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω),
      IsReb T n ψ → ∀ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p),
      (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp (p := p) (e t)) →
      v (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) < 1 →
      ∀ r : ℤ, v (∑ t, e t * zp Ω ((a t).coeff r)) < 1 := by
  intro p hp Ω _ _ hC v hv hvp T n ψ hψ d e a he hsum r
  have hq : p ^ n ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hqq : IsIntegral (O0 p) (T.qq n) :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hq) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  have hint : ∀ x, ψ x ∈ v.valuationSubring := by
    intro x
    have hx : ψ x ∈ ψ.range := ⟨x, rfl⟩
    rw [hψ.rng] at hx
    exact (hv _).2 (adjoin_le_integralClosure hqq hx)
  have hzp : ∀ z : ℤ_[p], ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C z)) = zp Ω z := by
    intro z
    refine hψ.sub _ _ (fun i => ?_) (fun r hr => ?_)
    · by_cases hi : i = 0
      · simp [hi]
      · have : (p : ℤ) ^ n * i ≠ 0 := mul_ne_zero (by exact_mod_cast hq) hi
        simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne this, HahnSeries.coeff_single_of_ne hi]
    · have : r ≠ 0 := by rintro rfl; exact hr (dvd_zero _)
      simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne this]
  let A := v.valuationSubring
  let k := IsLocalRing.ResidueField A
  let ρ : A →+* k := IsLocalRing.residue A
  have hρ : ∀ x : A, ρ x = 0 ↔ v (x : Ω) < 1 := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  let g : Lau p →+* A := (ψ.comp (algebraMap (Lau p) (O0 p))).codRestrict A (fun x => hint _)
  have hp0 : (p : k) = 0 := by
    rw [← map_natCast ρ, hρ]
    simpa using hvp
  have : CharP k p := (CharP.charP_iff_prime_eq_zero hp.out).2 hp0
  let : Algebra (ZMod p) k := ZMod.algebra k p
  have hker : RingHom.ker (LauZ.red p) ≤ RingHom.ker (ρ.comp g) := by
    intro x hx
    obtain ⟨y, rfl⟩ := (Basic.dvd_iff_map p x).2 hx
    rw [RingHom.mem_ker, map_mul, map_natCast, hp0, zero_mul]
  let φ : LaurentSeries (ZMod p) →+* k :=
    RingHom.liftOfRightInverse (LauZ.red p) (LauZ.lift p) (LauZ.red_lift p) ⟨ρ.comp g, hker⟩
  have hφ : ∀ x, φ (LauZ.red p x) = ρ (g x) := fun x =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ ⟨ρ.comp g, hker⟩ x
  have hCz : ∀ z : ℤ_[p], ρ (g (HahnSeries.C z)) = algebraMap (ZMod p) k (PadicInt.toZMod z) := by
    intro z
    have h1 : LauZ.red p (HahnSeries.C z) = HahnSeries.C (PadicInt.toZMod z) := by
      ext i
      rw [LauZ.red_coeff]
      by_cases hi : i = 0
      · simp [hi]
      · simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hi]
    rw [← hφ, h1]
    exact DFunLike.congr_fun (Subsingleton.elim (φ.comp HahnSeries.C) (algebraMap (ZMod p) k)) _
  let E : Fin d → A := fun t => ⟨e t, (hv _).2 (he t).1⟩
  let g0 : ℤ_[p] →+* A := g.comp HahnSeries.C
  have hg0 : (algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p)) = A.subtype.comp g0 := by
    ext z
    have h2 : algebraMap ℤ_[p] (O0 p) z = algebraMap (Lau p) (O0 p) (HahnSeries.single 0 z) := by
      rw [IsScalarTower.algebraMap_apply ℤ_[p] (Lau p) (O0 p)]
      congr 1
      ext i
      simp [HahnSeries.algebraMap_apply']
    show algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) z) = ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C z))
    rw [hzp, h2, zp]
  have exists_prim (P : ℤ_[p][X]) (hP : P ≠ 0) :
      ∃ (c : ℤ_[p]) (Q : ℤ_[p][X]), c ≠ 0 ∧ P = C c * Q ∧ Q.map (PadicInt.toZMod (p := p)) ≠ 0 := by
    classical
    let : NormalizedGCDMonoid ℤ_[p] := Classical.arbitrary _
    refine ⟨P.content, P.primPart, by rwa [Ne, content_eq_zero_iff], P.eq_C_content_mul_primPart, ?_⟩
    intro h0
    have hd : ∀ n, (p : ℤ_[p]) ∣ P.primPart.coeff n := by
      intro n
      have := congrArg (fun Q => Q.coeff n) h0
      simp only [coeff_map, coeff_zero] at this
      rwa [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
        Ideal.mem_span_singleton] at this
    exact PadicInt.prime_p.not_isUnit
      (isPrimitive_primPart P (p : ℤ_[p]) ((C_dvd_iff_dvd_coeff _ _).2 hd))
  have halg : ∀ t, IsAlgebraic (ZMod p) (ρ (E t)) := by
    intro t
    obtain ⟨P, hP, hPe⟩ := (he t).2
    obtain ⟨c, Q, hc, rfl, hQ⟩ := exists_prim P hP
    refine ⟨_, hQ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hg0, Polynomial.eval₂_mul, Polynomial.eval₂_C] at hPe
    have hc' : (A.subtype.comp g0) c ≠ 0 := by
      have : CharZero Ω := Basic.charZero_of_isClo hC
      obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc PadicInt.irreducible_p
      rw [map_mul, map_pow, map_natCast]
      exact mul_ne_zero (u.isUnit.map _).ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))
    have h1 := (mul_eq_zero.1 hPe).resolve_left hc'
    have h2 : Q.eval₂ g0 (E t) = 0 := by
      apply A.subtype_injective
      rw [Polynomial.hom_eval₂, map_zero]
      exact h1
    have h3 := congrArg ρ h2
    rw [Polynomial.hom_eval₂, map_zero] at h3
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← h3]
    congr 1
    ext z
    exact (hCz z).symm
  obtain ⟨f, hf, hfix⟩ := ResDisj.exists_pow_eq _ halg
  have hrel : ∑ t, ρ (E t) * φ (LauZ.red p (a t)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hφ, ← map_mul, ← map_sum]
    rw [hρ]
    convert hsum using 2
    exact map_sum A.subtype _ _
  have hres :=
    ResDisj.coeff_rel_of_pow φ hf _ hfix Finset.univ _ (fun t ht => absurd (Finset.mem_univ t) ht) hrel r
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LauZ.red_coeff, ← hCz, ← map_mul, ← map_sum] at hres
  rw [hρ] at hres
  convert hres using 2
  refine Eq.trans ?_ (map_sum A.subtype _ _).symm
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← hzp]
  rfl
