module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.CardClDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.MuIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.LevChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem cardLe_map_of_cardLe {R M N : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (S : Submodule R M) (n : ℕ) (h : CardLe S n) : CardLe (S.map f) n := by
  obtain ⟨hfin, hcard⟩ := h
  have hsurj : Function.Surjective
      (fun x : S => (⟨f x, Submodule.mem_map_of_mem x.2⟩ : S.map f)) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨Finite.of_surjective _ hsurj, (Nat.card_le_card_of_surjective _ hsurj).trans hcard⟩

theorem UpperTheory.V.Ws.exists_iwasawaRank_bound_of_ferreroWashington :
    UpperTheory.V.Published.FerreroWashington → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G ℚ Ω)), l ≠ 2 → IsOpen (U : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ U → U ≤ (cycMod ℚ Ω l 1).ker → ∃ r : ℕ, ∀ n : ℕ, XRk l 1 (levU l U n) r := by
  intro hFW Ω _ _ _ l _ U hl2 hUo hc hUcyc
  have hl : l.Prime := Fact.out
  have hUc : IsClosed (U : Set (G ℚ Ω)) := Subgroup.isClosed_of_isOpen U hUo
  set K : IntermediateField ℚ Ω := IntermediateField.fixedField U
  have hUK : K.fixingSubgroup = U := InfiniteGalois.fixingSubgroup_fixedField ⟨U, hUc⟩
  haveI : FiniteDimensional ℚ K := (InfiniteGalois.isOpen_iff_finite K).1 (by rw [hUK]; exact hUo)
  haveI : NumberField K := ⟨⟩
  have hgal : galOf ℚ K Ω = U := by
    rw [← hUK]
    ext σ
    simp [UpperTheory.V.Base.galOf, IntermediateField.mem_fixingSubgroup_iff]
  have hnorm : U.Normal := by
    constructor
    intro h hh g
    have hcm : g * h * g⁻¹ * h⁻¹ ∈ U :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h))
    have : g * h * g⁻¹ = (g * h * g⁻¹ * h⁻¹) * h := by group
    rw [this]
    exact U.mul_mem hcm hh
  haveI : IsGalois ℚ K := (InfiniteGalois.normal_iff_isGalois K).1 (by rw [hUK]; exact hnorm)
  haveI : IsMulCommutative Gal(K/ℚ) := by
    constructor
    constructor
    intro a b
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) Ω a
    obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) Ω b
    have hmem : σ * τ * σ⁻¹ * τ⁻¹ ∈ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) K).ker := by
      erw [IntermediateField.restrictNormalHom_ker K]
      rw [hUK]
      exact hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top σ) (Subgroup.mem_top τ))
    rw [MonoidHom.mem_ker] at hmem
    simp only [map_mul, map_inv] at hmem
    have h1 := congrArg (· * (AlgEquiv.restrictNormalHom K τ) * (AlgEquiv.restrictNormalHom K σ)) hmem
    simp only [one_mul, inv_mul_cancel_right] at h1
    exact h1
  haveI : IsAbelianGalois ℚ K := ⟨⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i : ℕ, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hl.ne_zero⟩
    infer_instance
  have hchar : ∀ σ : G ℚ Ω, cycMod ℚ Ω l 1 σ = 1 → galChar Ω (l ^ 1) σ = 1 := by
    intro σ h
    unfold ReciprocityTheory.Gal.cycMod ReciprocityTheory.Gal.cycZ at h
    unfold UpperTheory.V.Two.galChar
    rw [Units.ext_iff] at h ⊢
    simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at h
    erw [cyclotomicCharacter.toZModPow] at h
    exact h
  have hμ : ∃ ζ : K, IsPrimitiveRoot ζ (if l = 2 then 4 else l) := by
    rw [if_neg hl2]
    have := (muIff Ω K (l ^ 1)).2 (by
      rw [hgal]
      intro σ hσ
      exact hchar σ (hUcyc hσ))
    simpa only [pow_one] using this
  obtain ⟨r, hr⟩ := hFW l K hμ
  refine ⟨r, fun n => ?_⟩
  obtain ⟨hcyc, -, -⟩ := UpperTheory.V.Kum.fnCyc K Ω l n
  set K' := UpperTheory.V.Kum.Fn K Ω l n
  haveI : FiniteDimensional K K' := IsCyclotomicExtension.finiteDimensional {l ^ n} K K'
  haveI : FiniteDimensional ℚ K' := Module.Finite.trans K K'
  haveI : NumberField K' := ⟨⟩
  have hcl := hr n K'
  have hgo := UpperTheory.V.Kum.galOfCyc ℚ Ω l n K K'
  rw [hgal] at hgo
  have h2 : ∀ m : ZMod l, 2 • m = 0 → m = 0 := by
    intro m hm
    have h2ne : (2 : ZMod l) ≠ 0 := by
      intro h0
      have : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 this)
    rw [nsmul_eq_mul, Nat.cast_ofNat] at hm
    exact (mul_eq_zero.1 hm).resolve_left h2ne
  have hpull := UpperTheory.V.Kum.pullOnto ℚ Ω K' (levU l U n) hgo.ge 1 (ZMod l) (ZMod l) one_ne_zero hgo.le (Or.inr h2)
  show CardLe (UpperTheory.V.Kum.XDual 1 (levU l U n) (ZMod l) (ZMod l)) (l ^ r)
  rw [← hpull]
  apply cardLe_map_of_cardLe
  have cardLe_dual_zmod_card (l : ℕ) [Fact l.Prime] (V : Type) [AddCommGroup V] [Module (ZMod l) V]
      [Finite V] : CardLe (V →ₗ[ZMod l] ZMod l) (Nat.card V) := by
    refine ⟨Finite.of_injective (fun f : V →ₗ[ZMod l] ZMod l => (f : V → ZMod l)) DFunLike.coe_injective, ?_⟩
    show Nat.card (Module.Dual (ZMod l) V) ≤ _
    rw [Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq).toEquiv]

  have cardLe_hom (A : Type) [CommGroup A] [Finite A] (l : ℕ) [Fact l.Prime] (P : Type) (θ : P → A → ZMod l)
      (hθ : Function.Injective θ) (hm : ∀ p a b, θ p (a * b) = θ p a + θ p b) :
      CardLe P (Nat.card (A ⧸ (powMonoidHom l : A →* A).range)) := by
    have hpow : ∀ p (c : A) (n : ℕ), θ p (c ^ n) = n • θ p c := by
      intro p c n
      induction n with
      | zero =>
        have h := hm p 1 1
        rw [mul_one] at h
        simpa using h
      | succ n ih => rw [pow_succ, hm, ih, succ_nsmul]
    have h1 : ∀ p, θ p 1 = 0 := fun p => by simpa using hpow p 1 0
    have hV : ∀ v : Additive (A ⧸ (powMonoidHom l : A →* A).range), l • v = 0 := by
      intro v
      change (Additive.toMul v : A ⧸ (powMonoidHom l : A →* A).range) ^ l = 1
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
      rw [← ha, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨a, rfl⟩
    let φ : P → A →* Multiplicative (ZMod l) := fun p =>
      { toFun := fun a => Multiplicative.ofAdd (θ p a)
        map_one' := by
          show Multiplicative.ofAdd (θ p 1) = 1
          rw [h1]
          rfl
        map_mul' := fun a b => by
          show Multiplicative.ofAdd (θ p (a * b)) = _
          rw [hm]
          rfl }
    let ψ : P → (A ⧸ (powMonoidHom l : A →* A).range) →* Multiplicative (ZMod l) := fun p =>
      QuotientGroup.lift _ (φ p) (by
        rintro _ ⟨c, rfl⟩
        show Multiplicative.ofAdd (θ p (c ^ l)) = 1
        rw [hpow, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
        rfl)
    let Φ : P → (Additive (A ⧸ (powMonoidHom l : A →* A).range) →+ ZMod l) := fun p =>
      AddMonoidHom.mk' (fun v => Multiplicative.toAdd (ψ p (Additive.toMul v))) (fun u v => by
        show Multiplicative.toAdd (ψ p (Additive.toMul u * Additive.toMul v)) = _
        rw [map_mul]
        rfl)
    have hΦ : ∀ p (a : A), Φ p (Additive.ofMul (QuotientGroup.mk a)) = θ p a := fun p a => rfl
    have hinj : Function.Injective Φ := by
      intro p q h
      apply hθ
      funext a
      rw [← hΦ p a, ← hΦ q a, h]
    letI : Module (ZMod l) (Additive (A ⧸ (powMonoidHom l : A →* A).range)) := AddCommGroup.zmodModule hV
    exact CardLe.of_injective (cardLe_dual_zmod_card l (Additive (A ⧸ (powMonoidHom l : A →* A).range))) _
      ((AddMonoidHom.toZModLinearMap_injective l (M := Additive (A ⧸ (powMonoidHom l : A →* A).range))
        (M₁ := ZMod l)).comp hinj)
  have hcard : CardLe (UpperTheory.V.Kum.ClDual K' 1 (ZMod l) (ZMod l))
      (Nat.card (ClassGroup (𝓞 K') ⧸ (powMonoidHom l : ClassGroup (𝓞 K') →* ClassGroup (𝓞 K')).range)) := by
    exact cardLe_hom (ClassGroup (𝓞 K')) l _ (fun θ => θ.1) Subtype.val_injective fun θ => θ.2.1
  obtain ⟨hf, hle⟩ := hcard
  exact ⟨hf, hle.trans hcl⟩
