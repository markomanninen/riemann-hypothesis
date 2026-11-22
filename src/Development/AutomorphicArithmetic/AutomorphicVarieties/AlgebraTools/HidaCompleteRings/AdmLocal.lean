module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.AdmFin

@[expose] public section

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordAdm_maximalIdeal_and_finite_quotients :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Module.Finite R M], OrdAdm (M := M) (IsLocalRing.maximalIdeal R) ∧ (Finite (IsLocalRing.ResidueField R) → ∀ k : ℕ, Finite (M ⧸ (IsLocalRing.maximalIdeal R ^ k • ⊤ : Submodule R M))) := by
  intro R _ M _ _ _ _ _ _
  haveI : IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R) := by
    letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
    infer_instance
  have hOrd : OrdAdm (M := M) (IsLocalRing.maximalIdeal R) := by
    refine ⟨UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.completeFin (IsLocalRing.maximalIdeal R), fun k => ?_⟩
    have hMax {I : Ideal R} [IsArtinianRing (R ⧸ I)] (P : Ideal R) [P.IsPrime]
        (h : I ≤ P) : P.IsMaximal := by
      have h1 : (P.map (Ideal.Quotient.mk I)).IsPrime :=
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
      have h2 : (P.map (Ideal.Quotient.mk I)).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
      have h3 := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
        (K := P.map (Ideal.Quotient.mk I))
      rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.2 h] at h3
    have hArtPow (k : ℕ) : IsArtinianRing (R ⧸ IsLocalRing.maximalIdeal R ^ k) := by
      rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
      intro p hp
      have h0 : IsLocalRing.maximalIdeal R ^ k ≤ p.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k)) := by
        intro x hx
        simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      have h1 : (p.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k))).IsMaximal :=
        hMax _ (Ideal.IsPrime.le_of_pow_le h0)
      have h2 := Ideal.map_comap_of_surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k))
        Ideal.Quotient.mk_surjective p
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ k))
          Ideal.Quotient.mk_surjective h1 with h | h
      · exact absurd (h2 ▸ h) hp.ne_top
      · exact h2 ▸ h
    haveI := hArtPow k
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    refine ⟨inferInstance, ?_⟩
    haveI : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R ^ k)
        (M ⧸ (IsLocalRing.maximalIdeal R ^ k • ⊤ : Submodule R M)) :=
      Module.Finite.of_restrictScalars_finite R _ _
    exact isArtinian_of_surjective_algebraMap (R := R ⧸ IsLocalRing.maximalIdeal R ^ k)
      Ideal.Quotient.mk_surjective
  refine ⟨hOrd, fun hfin k => ?_⟩
  haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) := hfin
  haveI : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M
  induction k with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    infer_instance
  | succ n ih =>
    rw [pow_succ', Submodule.mul_smul]
    exact Submodule.finite_quotient_smul _ (IsNoetherian.noetherian _)
