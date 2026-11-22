module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.AutP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.Temper
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsCalcP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistenceOfGaloisRepresentationsOfHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.SignFix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UntwistS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FlagPol
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open scoped Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem place_under {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {p : ℕ}
    (hp0 : p ≠ 0) (hp : A.valuation (p : Ω) < 1) :
    ∃ w : HeightOneSpectrum (𝓞 F), IsPlaceOver A w ∧ (p : 𝓞 F) ∈ w.asIdeal := by
  have hA : ∀ x : 𝓞 F, algebraMap F Ω (x : F) ∈ A := fun x => by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
      ((x.isIntegral_coe.map (algebraMap F Ω).toIntAlgHom).tower_top : IsIntegral A (algebraMap F Ω (x : F)))
    exact hy ▸ y.2
  let f : 𝓞 F →+* A := ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).codRestrict A hA
  have hf : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ (IsLocalRing.maximalIdeal A).comap f := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hm : (p : 𝓞 F) ∈ (IsLocalRing.maximalIdeal A).comap f := (hf _).1 (by simpa only [map_natCast] using hp)
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun h => ?_⟩, hf, hm⟩
  rw [h, Ideal.mem_bot] at hm
  exact hp0 (Nat.cast_eq_zero.1 hm)

private theorem pow_eq_one_of_kills {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    {M : ℕ} (hM : 1 ≤ M) : ∃ k : ℕ, 0 < k ∧ ∀ (C : Type) [Monoid C] (χ : G F Ω →* C), KillsMu M χ → ∀ s, χ s ^ k = 1 := by
  let S : SubMulAction (G F Ω) Ω :=
    { carrier := {ζ | ζ ^ M = 1}
      smul_mem' := fun s ζ (h : ζ ^ M = 1) => by
        show (s ζ) ^ M = 1
        rw [← map_pow, h, map_one] }
  haveI : Finite S := by
    classical
    refine Set.Finite.subset (s := ((nthRoots M (1 : Ω)).toFinset : Set Ω)) (Finset.finite_toSet _) fun ζ h => ?_
    exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 ((mem_nthRoots hM).2 h))
  refine ⟨Nat.card (Equiv.Perm S), Nat.card_pos, fun C _ χ h s => ?_⟩
  rw [← map_pow]
  refine h _ fun ζ hζ => ?_
  have e : MulAction.toPermHom (G F Ω) S (s ^ Nat.card (Equiv.Perm S)) = 1 := by
    rw [map_pow, pow_card_eq_one']
  exact congrArg Subtype.val (DFunLike.congr_fun e ⟨ζ, hζ⟩)

private theorem charpoly_of_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} {r : H →* GL (Fin n) k}
    {κ : Fin n → H →* kˣ} (h : W.HasFlag r κ) (s : H) (b : GL (Fin n) k) :
    ((b * r s * b⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = ∏ i, (X - C ((κ i s : kˣ) : k)) := by
  obtain ⟨a, ha⟩ := h
  have h1 := Matrix.charpoly_of_upperTriangular ((a * r s * a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
    fun i j hij => (ha s).1 i j hij
  simp only [(ha s).2] at h1
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
