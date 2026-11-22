module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlfrob
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IrreducibleWeilDeligneTameLevelEqCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InertiaFixesRootsOfUnityOfArtinCongruence
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelNontrivialOfCharacterSupport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelExistsTorusCongruenceFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixedCongruenceNeBotOfJacquetTorusFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasFixedOfAlgNormFixedNeBot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemMaximalCompactAndCongruentOfMemPrincipalCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeMatchBaseChange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unliso

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.GalN.V

private theorem val_le_one {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (A : ValuationSubring Ω) (x : 𝓞 K) : A.valuation (algebraMap K Ω (x : K)) ≤ 1 := by
  have hi : IsIntegral ℤ (algebraMap K Ω (x : K)) := (x.2 : IsIntegral ℤ (x : K)).map (IsScalarTower.toAlgHom ℤ K Ω)
  have hA : IsIntegral A (algebraMap K Ω (x : K)) := hi.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hA
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

private theorem exists_place {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω]
    [Algebra F Ω] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A w) :
    ∃ v : HeightOneSpectrum (𝓞 K), IsPlaceOver A v := by
  let I : Ideal (𝓞 K) :=
    { carrier := {x | A.valuation (algebraMap K Ω (x : K)) < 1}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        have e : algebraMap K Ω ((a + b : 𝓞 K) : K) = algebraMap K Ω (a : K) + algebraMap K Ω (b : K) := by
          simp
        rw [e]
        exact Valuation.map_add_lt _ ha hb
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have e : algebraMap K Ω ((c • a : 𝓞 K) : K) = algebraMap K Ω (c : K) * algebraMap K Ω (a : K) := by
          simp
        rw [e, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_le_one A c)) ha }
  have hmem : ∀ x : 𝓞 K, x ∈ I ↔ A.valuation (algebraMap K Ω (x : K)) < 1 := fun _ => Iff.rfl
  have hprime : I.IsPrime := by
    refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
    · have := (hmem 1).1 (h ▸ Submodule.mem_top)
      simp at this
    · rw [hmem] at hab
      by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2⟩ := hcon
      rw [hmem, not_lt] at h1 h2
      have e1 := le_antisymm (val_le_one A a) h1
      have e2 := le_antisymm (val_le_one A b) h2
      have e : algebraMap K Ω ((a * b : 𝓞 K) : K) = algebraMap K Ω (a : K) * algebraMap K Ω (b : K) := by
        simp
      rw [e, map_mul, e1, e2] at hab
      simp at hab
  have hne : I ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    intro hI
    have h1 : A.valuation (algebraMap F Ω (x : F)) < 1 := (hA x).2 hx
    have h2 : algebraMap (𝓞 F) (𝓞 K) x ∈ I := by
      rw [hmem]
      rw [IsScalarTower.algebraMap_apply F K Ω] at h1
      exact h1
    rw [hI, Ideal.mem_bot] at h2
    exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by simpa using h2))
  exact ⟨⟨I, hprime, hne⟩, fun x => (hmem x).symm⟩
