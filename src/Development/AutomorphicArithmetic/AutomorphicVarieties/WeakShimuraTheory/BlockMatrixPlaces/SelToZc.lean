module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem exists_norm {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (hρ : ContAction ρ)
    (h2 : Function.Surjective fun m : M => m + m) (c : Γ) (hc : ∀ m, ρ c m = -m) (x : H1 ρ) :
    ∃ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) = x ∧ z.1 c = 0 := by
  obtain ⟨z0, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, hm⟩ := h2 (-(z0.1 c))
  have hB : d0 ρ m ∈ Z1 ρ := coboundaries_le_cocycles ρ hρ (LinearMap.mem_range_self _ m)
  refine ⟨z0 - ⟨d0 ρ m, hB⟩, ?_, ?_⟩
  · rw [Submodule.Quotient.eq, Submodule.mem_comap, sub_sub_cancel_left, map_neg]
    exact Submodule.neg_mem _ ⟨m, rfl⟩
  · show z0.1 c - d0 ρ m c = 0
    rw [amitsur_d0_apply, hc]
    have hm' : m + m = -(z0.1 c) := hm
    calc z0.1 c - (-m - m) = z0.1 c + (m + m) := by abel
      _ = 0 := by rw [hm']; abel

theorem UpperTheory.V.Ws.Bl.selToZc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ρ : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), ContAction ρ → (Function.Bijective fun m : M => m + m) →
          ∀ c : G ℚ Ω, (∀ m, ρ (toGS Ω _ c) m = -m) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) →
          ∀ v0 : S, ((l : ℕ) : 𝓞 ℚ) ∈ v0.1.asIdeal → ∀ (P : Set M) (K : Subgroup (G ℚ Ω)), (∀ g ∈ K, ∀ m, ρ (toGS Ω _ g) m = m) →
          ∀ L : LocCond ρ (locFam S Av), (∀ v, v ≠ v0 → L v ≤ H1ur (ρ.comp (locFam S Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v)))) →
          (∀ z : Z1 (ρ.comp (locFam S Av v0)), (Submodule.Quotient.mk z : H1 (ρ.comp (locFam S Av v0))) ∈ L v0 → ∃ y, ∀ h, z.1 h - (ρ (locFam S Av v0 h) y - y) ∈ P) →
          ∃ f : Sel ρ (locFam S Av) (continuous_locFam S Av) L → Zc (fun g m => ρ (toGS Ω _ g) m) c (neSet l K) (Dec (F := ℚ) (Av v0)) P, Function.Injective f := by
  intro Ω _ _ _ l _ R M _ _ _ _ _ S ρ hρ hbij c hcneg Av hAv v0 hlv0 P K hK L hL hP
  have val_top {Ω : Type} [Field Ω] {x : Ω} (h : (⊤ : ValuationSubring Ω).valuation x < 1) : x = 0 := by
    by_contra hx
    have h1 : (⊤ : ValuationSubring Ω).valuation x⁻¹ ≤ 1 :=
      (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
    have h2 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h h1
    rw [← map_mul, mul_inv_cancel₀ hx, map_one] at h2
    exact lt_irrefl _ h2

  have int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
      A.valuation b ≤ 1 := by
    have h : IsIntegral A b := hb.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [A.valuation_le_one_iff, ← hy]
    exact y.2

  have exists_place (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
      (A : ValuationSubring Ω) (hA : A ≠ ⊤) : ∃ v : HeightOneSpectrum (𝓞 K),
        ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ v.asIdeal := by
    have hm : ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A := fun x =>
      (A.valuation_le_one_iff _).1 (int_le A (x.isIntegral_coe.map (algebraMap K Ω).toIntAlgHom))
    let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hm
    let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f
    have hP : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ P := fun x =>
      (A.valuation_lt_one_iff (f x)).symm
    refine ⟨⟨P, inferInstance, fun h0 => hA ?_⟩, hP⟩
    rw [eq_top_iff]
    intro x _
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
    have h1 : Algebra.IsAlgebraic ℤ K := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := K)).2 inferInstance
    have h2 : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ K Ω
    obtain ⟨n, hn, hi⟩ := (h2.isAlgebraic x).exists_integral_multiple
    have h3 : ¬ A.valuation (algebraMap K Ω ((n : 𝓞 K) : K)) < 1 := by
      rw [hP, h0, Ideal.mem_bot]
      exact Int.cast_ne_zero.2 hn
    have h4 : A.valuation (n : Ω) = 1 :=
      le_antisymm (int_le A (isIntegral_algebraMap (R := ℤ) (x := n))) (by simpa using h3)
    have h5 := int_le A hi
    rw [zsmul_eq_mul, map_mul, h4, one_mul] at h5
    exact (A.valuation_le_one_iff x).1 h5

  have placeDict : Ine (F := ℚ) (⊤ : ValuationSubring Ω) = ⊥ ∧
      (∀ A : ValuationSubring Ω, A ≠ ⊤ → ∃ v : HeightOneSpectrum (𝓞 ℚ), IsPlaceOver A v) := by
    refine ⟨?_, fun A hA => exists_place ℚ Ω A hA⟩
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext x
    have h := hg.2 x ((ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _))
    exact sub_eq_zero.1 (val_top h)
  have hex : ∀ x : H1 ρ, ∃ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) = x ∧ z.1 (toGS Ω _ c) = 0 :=
    fun x => exists_norm ρ hρ hbij.2 (toGS Ω _ c) hcneg x
  have hA : ∀ x : H1 ρ, x ∈ Sel ρ (locFam S Av) (continuous_locFam S Av) L → ∀ z : Z1 ρ,
      (Submodule.Quotient.mk z : H1 ρ) = x → z.1 (toGS Ω _ c) = 0 →
      (fun g => z.1 (toGS Ω _ g)) ∈ Zc (fun g m => ρ (toGS Ω _ g) m) c (neSet l K) (Dec (F := ℚ) (Av v0)) P := by
    intro x hx z hzx hzc
    subst hzx
    have hcoc : ∀ g h, z.1 (g * h) = z.1 g + ρ g (z.1 h) := ((mem_Z1_iff_cocycle _ _).mp z.2).2
    have hz1 : z.1 1 = 0 := by
      have h := hcoc 1 1
      rw [one_mul, map_one, Module.End.one_apply] at h
      simpa using h
    have hmemv : ∀ v, (Submodule.Quotient.mk (restrictCocycles1 ρ (locFam S Av v) (continuous_locFam S Av v) z) :
        H1 (ρ.comp (locFam S Av v))) ∈ L v := fun v => (mem_Sel _ _ _ _ _).mp hx v
    obtain ⟨y, hy⟩ := hP _ (hmemv v0)
    refine ⟨y, ⟨?_, ?_, hzc, ?_, ?_⟩⟩
    · exact ((IsLocallyConstant.iff_continuous _).mpr ((mem_Z1_iff_cocycle _ _).mp z.2).1).comp_continuous
        continuous_quot_mk
    · intro g h
      show z.1 (toGS Ω _ (g * h)) = z.1 (toGS Ω _ g) + ρ (toGS Ω _ g) (z.1 (toGS Ω _ h))
      rw [map_mul]
      exact hcoc _ _
    · rintro g ⟨hgK, A, hAl, hgA⟩
      show z.1 (toGS Ω _ g) = 0
      by_cases hAtop : A = ⊤
      · subst hAtop
        rw [(placeDict).1, Subgroup.mem_bot] at hgA
        rw [hgA, map_one, hz1]
      obtain ⟨v, hAv'⟩ := (placeDict).2 A hAtop
      by_cases hvS : v ∈ S
      · set w : S := ⟨v, hvS⟩
        have hne : w ≠ v0 := by
          intro hw
          apply hAl
          have h := (hAv' (l : 𝓞 ℚ)).mpr (by rw [show v = v0.1 from congrArg Subtype.val hw]; exact hlv0)
          simpa using h
        obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hAv w) hAv'
        rw [← hσ] at hgA
        have hgA' : σ⁻¹ * g * σ ∈ Ine (F := ℚ) (Av w) := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hgA
        have hur := hL w hne (hmemv w)
        rw [H1ur, LinearMap.mem_ker] at hur
        have hur' := (Submodule.Quotient.mk_eq_zero _).mp hur
        rw [Submodule.mem_comap] at hur'
        obtain ⟨m, hm⟩ := hur'
        have hj := congrFun hm ⟨⟨σ⁻¹ * g * σ, Ine_le_Dec _ hgA'⟩, hgA'⟩
        rw [amitsur_d0_apply] at hj
        have hconj : z.1 (toGS Ω _ (σ⁻¹ * g * σ)) = 0 := by
          have hj' : z.1 (toGS Ω _ (σ⁻¹ * g * σ)) = ρ (toGS Ω _ (σ⁻¹ * g * σ)) m - m := hj.symm
          rw [hj']
          rw [map_mul, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
            show ρ (toGS Ω _ g) (ρ (toGS Ω _ σ) m) = ρ (toGS Ω _ σ) m from hK g hgK _,
            ← Module.End.mul_apply, ← map_mul, map_inv, inv_mul_cancel, map_one, Module.End.one_apply, sub_self]
        set a := toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) σ
        set b := toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g
        have hb : ∀ m, ρ b m = m := hK g hgK
        rw [map_mul, map_mul, map_inv] at hconj
        have e1 := hcoc (a⁻¹ * b) a
        have e2 := hcoc a⁻¹ b
        have e3 := hcoc a⁻¹ a
        rw [inv_mul_cancel, hz1] at e3
        rw [map_mul, Module.End.mul_apply, hb, e2, hconj] at e1
        have hinv0 : ρ a⁻¹ (z.1 b) = 0 := by
          have : (0 : M) = ρ a⁻¹ (z.1 b) + (z.1 a⁻¹ + ρ a⁻¹ (z.1 a)) := by rw [e1]; abel
          rw [← e3, add_zero] at this
          exact this.symm
        have : z.1 b = ρ a (ρ a⁻¹ (z.1 b)) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        rw [this, hinv0, map_zero]
      · have hgN : g ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) :=
          Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure
            (Set.mem_iUnion₂.mpr ⟨v, hvS, Set.mem_iUnion₂.mpr ⟨A, hAv', hgA⟩⟩))
        rw [show toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g = 1 from (QuotientGroup.eq_one_iff g).mpr hgN, hz1]
    · intro h hh
      exact hy ⟨h, hh⟩
  choose zc hzc using hex
  refine ⟨fun x => ⟨fun g => (zc x.1).1 (toGS Ω _ g), hA x.1 x.2 (zc x.1) (hzc x.1).1 (hzc x.1).2⟩, ?_⟩
  intro x x' hxx
  have hfun : (fun g => (zc x.1).1 (toGS Ω _ g)) = (fun g => (zc x'.1).1 (toGS Ω _ g)) :=
    congrArg Subtype.val hxx
  have hz : zc x.1 = zc x'.1 := by
    apply Subtype.ext
    funext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) q
    exact congrFun hfun g
  apply Subtype.ext
  rw [← (hzc x.1).1, ← (hzc x'.1).1, hz]
