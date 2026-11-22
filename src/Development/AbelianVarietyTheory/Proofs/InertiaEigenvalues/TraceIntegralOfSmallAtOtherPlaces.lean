module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped WithZero

namespace GlobalTheory.TraceSmall

theorem valV_le_one_of_ext {T T' : CDVR} (i : T.Fr →+* T'.Fr) {e' : ℕ} (he' : 0 < e')
    (hv : ∀ z : T.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T.V z) (z : T.Fr) :
    valV T'.V (i z) ≤ 1 ↔ valV T.V z ≤ 1 := by
  by_cases hz : z = 0
  · subst hz; simp
  have h1 : valV T'.V (i z) ≠ 0 := valV_ne_zero ((map_ne_zero i).2 hz)
  have h2 : valV T.V z ≠ 0 := valV_ne_zero hz
  have h := hv z hz
  have he : (0 : ℤ) < e' := by exact_mod_cast he'
  rw [← WithZero.log_le_log h1 one_ne_zero, ← WithZero.log_le_log h2 one_ne_zero, WithZero.log_one]
  unfold vV at h
  constructor <;> intro h' <;> nlinarith

theorem exists_bound {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (p : HeightOneSpectrum (𝓞 K)) {m : ℕ} (y : Fin m → L) :
    ∃ N : ℕ, ∀ la' : HeightOneSpectrum (𝓞 L), la'.asIdeal.under (𝓞 K) = p.asIdeal → ∀ k,
      la'.valuation L (y k) ≤ WithZero.exp (N : ℤ) := by
  have hS : {la' : HeightOneSpectrum (𝓞 L) | la'.asIdeal.under (𝓞 K) = p.asIdeal}.Finite := by
    refine (Set.Finite.preimage (f := fun la' : HeightOneSpectrum (𝓞 L) => la'.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
      (IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 L))).subset fun la' h => ?_
    exact ⟨la'.isPrime, ⟨h.symm⟩⟩
  obtain ⟨B, hB⟩ := ((hS.prod (Set.finite_univ (α := Fin m))).image
    fun q : HeightOneSpectrum (𝓞 L) × Fin m => WithZero.log (q.1.valuation L (y q.2))).bddAbove
  refine ⟨B.toNat, fun la' h k => ?_⟩
  by_cases hy : y k = 0
  · simp [hy]
  have h0 : la'.valuation L (y k) ≠ 0 := by simpa using hy
  have := hB ⟨(la', k), ⟨h, Set.mem_univ _⟩, rfl⟩
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
  simp only at this
  omega

theorem valuation_le_of_mem {L : Type} [Field L] [NumberField L] (la' : HeightOneSpectrum (𝓞 L)) {N : ℕ}
    {b : 𝓞 L} (hb : b ∈ la'.asIdeal ^ N) : la'.valuation L (b : L) ≤ WithZero.exp (-(N : ℤ)) :=
  (la'.valuation_of_algebraMap b).trans_le ((la'.intValuation_le_pow_iff_mem b N).2 hb)

theorem trace_le_one : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ (m : ℕ) (y : Fin m → L), ∃ N : ℕ, ∀ b : 𝓞 L, (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal → b ∈ la'.asIdeal ^ N) → ∀ (T : CDVR), T.FinRes → ∀ (io : K →+* T.Fr) (e : ℕ), OverLa p T.V io e → ∀ x : Fin m → T.Fr, (∀ k, valV T.V (x k) ≤ 1) → (∀ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e' : ℕ) (τ : L →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T.V z) → T'.FinRes → (∀ z : K, τ (algebraMap K L z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (x k)) ≤ 1) → valV T.V (∑ k, io (Algebra.trace K L ((b : L) * y k)) * x k) ≤ 1 := by
  intro K L _ _ _ _ _ p la hla m y
  obtain ⟨N, hN⟩ := exists_bound p y
  refine ⟨N, fun b hb T hT io e ho x hx H => ?_⟩
  let Ω := AlgebraicClosure L
  let F := IntermediateField.normalClosure K L Ω
  obtain ⟨T', i, e', σ₀, he', hv, hT', hσ₀⟩ := GlobalTheory.SupDescent.exists_ext (L := F) T hT io
  have hv' : ∀ a : T.Fr, vV T'.V (i a) = (e' : ℤ) * vV T.V a := fun a => by
    by_cases h : a = 0
    · subst h; simp [vV]
    · exact hv a h
  have ho' := ho.bc i he' hv'
  have hF : ∀ (ρ : L →ₐ[K] Ω) (z : L), ρ z ∈ F := fun ρ z =>
    AlgHom.fieldRange_le_normalClosure ρ ⟨z, rfl⟩
  let τ : (L →ₐ[K] Ω) → L →+* T'.Fr := fun ρ =>
    σ₀.comp ((ρ.codRestrict F.toSubalgebra (hF ρ)).toRingHom)
  have hτ : ∀ ρ z, τ ρ z = σ₀ ⟨ρ z, hF ρ z⟩ := fun _ _ => rfl
  have hτK : ∀ ρ (a : K), τ ρ (algebraMap K L a) = i (io a) := fun ρ a => by
    rw [hτ, ← hσ₀ a]
    congr 1
    exact Subtype.ext (ρ.commutes a)
  have htr : ∀ z : L, i (io (Algebra.trace K L z)) = ∑ ρ : L →ₐ[K] Ω, τ ρ z := fun z => by
    have h1 := trace_eq_sum_embeddings Ω (K := K) (L := L) (x := z)
    have h2 : algebraMap K F (Algebra.trace K L z) = ∑ ρ : L →ₐ[K] Ω, (⟨ρ z, hF ρ z⟩ : F) := by
      apply Subtype.val_injective
      rw [IntermediateField.coe_sum]
      exact h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hσ₀, h2, map_sum]
    exact Finset.sum_congr rfl fun ρ _ => (hτ ρ z).symm
  rw [← valV_le_one_of_ext i he' hv]
  have hsum : i (∑ k, io (Algebra.trace K L ((b : L) * y k)) * x k) =
      ∑ ρ : L →ₐ[K] Ω, ∑ k, τ ρ (b : L) * (τ ρ (y k) * i (x k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul (f := i), htr, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, mul_assoc]
  rw [hsum]
  refine Valuation.map_sum_le _ fun ρ _ => ?_
  have hunit (v : T'.V) : valV T'.V (algebraMap T'.V T'.Fr v) = 1 ↔ IsUnit v := by
    have hlt : valV T'.V (algebraMap T'.V T'.Fr v) < 1 ↔ v ∈ IsLocalRing.maximalIdeal T'.V := HeightOneSpectrum.valuation_lt_one_iff_mem _ v
    rw [← IsLocalRing.notMem_maximalIdeal, ← hlt, not_lt]
    exact ⟨fun h => h.ge, fun h => le_antisymm (HeightOneSpectrum.valuation_le_one _ v) h⟩
  have hpos_aux {v : T'.V} (h0 : v ≠ 0) (h : v ∈ IsLocalRing.maximalIdeal T'.V) :
      0 < vV T'.V (algebraMap T'.V T'.Fr v) := by
    have h1 : algebraMap T'.V T'.Fr v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective T'.V T'.Fr)).2 h0
    have h2 := (WithZero.log_lt_log (valV_ne_zero (V := T'.V) h1) one_ne_zero).2
      ((HeightOneSpectrum.valuation_lt_one_iff_mem _ v).2 h)
    simp only [WithZero.log_one] at h2
    simp only [vV]; omega
  have hex : ∃ (la : HeightOneSpectrum (𝓞 L)) (e : ℕ), OverLa la T'.V (τ ρ) e := by
    have hint : ∀ a : 𝓞 L, ∃ v : T'.V, algebraMap T'.V T'.Fr v = (τ ρ) a := fun a =>
      IsIntegrallyClosed.algebraMap_eq_of_integral (R := T'.V) (K := T'.Fr)
        (IsIntegral.map_of_comp_eq (Int.castRingHom T'.V) (τ ρ) (RingHom.ext_int _ _) a.isIntegral_coe)
    choose g0 hg0 using hint
    have hinj := IsFractionRing.injective T'.V T'.Fr
    let g : 𝓞 L →+* T'.V :=
      { toFun := g0
        map_one' := hinj (by simp [hg0])
        map_mul' := fun a b => hinj (by simp [hg0])
        map_zero' := hinj (by simp [hg0])
        map_add' := fun a b => hinj (by simp [hg0]) }
    have hg : ∀ a, algebraMap T'.V T'.Fr (g a) = (τ ρ) (algebraMap (𝓞 L) L a) := hg0
    have hne : (IsLocalRing.maximalIdeal T'.V).comap g ≠ ⊥ := by
      have : Finite (IsLocalRing.ResidueField T'.V) := hT'
      have hc : Nat.card (IsLocalRing.ResidueField T'.V) ≠ 0 := Nat.card_pos.ne'
      intro h
      have h1 : ((Nat.card (IsLocalRing.ResidueField T'.V) : ℕ) : 𝓞 L) ∈ (IsLocalRing.maximalIdeal T'.V).comap g := by
        rw [Ideal.mem_comap, map_natCast, ← IsLocalRing.residue_eq_zero_iff, map_natCast, ← nsmul_one]
        exact card_nsmul_eq_zero'
      rw [h, Ideal.mem_bot] at h1
      exact hc (by exact_mod_cast h1)
    let la : HeightOneSpectrum (𝓞 L) := ⟨(IsLocalRing.maximalIdeal T'.V).comap g, Ideal.comap_isPrime _ _, hne⟩
    have hun : ∀ a : 𝓞 L, a ∉ la.asIdeal → valV T'.V ((τ ρ) (algebraMap (𝓞 L) L a)) = 1 := fun a ha => by
      rw [← hg, hunit]
      exact IsLocalRing.notMem_maximalIdeal.1 ha
    have hone : ∀ x : L, la.valuation L x = 1 → valV T'.V ((τ ρ) x) = 1 := fun x hx => by
      obtain ⟨n, d, h⟩ := la.exists_primeCompl_mul_eq_of_integer x hx.le
      have hd : la.valuation L (algebraMap (𝓞 L) L d) = 1 := (la.valuation_eq_one_iff_notMem).2 d.2
      have hn : la.valuation L (algebraMap (𝓞 L) L n) = 1 := by rw [← h, map_mul, hx, hd, one_mul]
      have h2 := hun n ((la.valuation_eq_one_iff_notMem).1 hn)
      rwa [← h, map_mul, map_mul, hun d d.2, mul_one] at h2
    obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
    have hπK : la.valuation L (algebraMap (𝓞 L) L π) = WithZero.exp (-1 : ℤ) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, hπ]
    have hπ0 : algebraMap (𝓞 L) L π ≠ 0 := fun h => by simp [h] at hπK; exact WithZero.exp_ne_zero hπK.symm
    have hπm : π ∈ la.asIdeal := by
      rw [← la.valuation_lt_one_iff_mem (K := L), hπK, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    have hpos : 0 < vV T'.V ((τ ρ) (algebraMap (𝓞 L) L π)) := by
      rw [← hg]
      refine hpos_aux (fun h => ?_) hπm
      have := hg π
      rw [h, map_zero] at this
      exact (map_ne_zero (τ ρ)).2 hπ0 this.symm
    refine ⟨la, (vV T'.V ((τ ρ) (algebraMap (𝓞 L) L π))).toNat, by omega, fun a => ?_⟩
    rw [Int.toNat_of_nonneg hpos.le]
    by_cases ha : a = 0
    · simp [ha, vV, vLa]
    have hva : la.valuation L a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
    have h1 := hone (a * (algebraMap (𝓞 L) L π) ^ (-vLa la a)) (by
      rw [map_mul, map_zpow₀, hπK, ← WithZero.exp_zsmul, ← WithZero.exp_log hva, ← WithZero.exp_add]
      simp [vLa])
    have h2 := congrArg WithZero.log h1
    rw [map_mul, map_mul, map_zpow₀, map_zpow₀, WithZero.log_mul (valV_ne_zero ((map_ne_zero (τ ρ)).2 ha))
      (zpow_ne_zero _ (valV_ne_zero ((map_ne_zero (τ ρ)).2 hπ0))), WithZero.log_zpow, WithZero.log_one] at h2
    simp only [vV, smul_eq_mul] at h2 ⊢
    linarith
  obtain ⟨la', e'', hol⟩ := hex
  have hunder : la'.asIdeal.under (𝓞 K) = p.asIdeal := Ideal.ext fun a => by
    rw [Ideal.under_def, Ideal.mem_comap, ← GlobalTheory.SupDescent.val_lt_one_iff_mem hol,
      ← GlobalTheory.SupDescent.val_lt_one_iff_mem ho']
    exact Iff.of_eq (congrArg (fun t => valV T'.V t < 1) (hτK ρ a))
  rcases eq_or_ne la' la with rfl | hne
  · rw [← Finset.mul_sum, map_mul]
    exact mul_le_one' ((GlobalTheory.SupDescent.val_le_one_iff hol _).2 (la'.valuation_le_one b))
      (H T' i e' (τ ρ) e'' he' hv hT' (hτK ρ) hol)
  · refine Valuation.map_sum_le _ fun k _ => ?_
    rw [← mul_assoc, ← map_mul, map_mul]
    refine mul_le_one' ((GlobalTheory.SupDescent.val_le_one_iff hol _).2 ?_) ((valV_le_one_of_ext i he' hv _).2 (hx k))
    rw [map_mul]
    calc la'.valuation L (b : L) * la'.valuation L (y k)
        ≤ WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ) :=
          mul_le_mul' (valuation_le_of_mem la' (hb la' hne hunder)) (hN la' hunder k)
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]

end GlobalTheory.TraceSmall
