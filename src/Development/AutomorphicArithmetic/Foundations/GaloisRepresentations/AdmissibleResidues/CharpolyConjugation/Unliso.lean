module

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

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.GalN UpperTheory.GalN.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem isRoot_map_equiv {k : Type} [Field k] (ι : k ≃+* ℂ) (p : Polynomial k) (x : k) :
    (p.map ι.toRingHom).IsRoot (ι x) ↔ p.IsRoot x := by
  have h : (p.map ι.toRingHom).eval (ι x) = ι (p.eval x) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply ι.toRingHom x
  rw [Polynomial.IsRoot.def, Polynomial.IsRoot.def, h]
  exact map_eq_zero_iff ι ι.injective

private theorem isRoot_charpoly_smul {k : Type} [Field k] {n : ℕ} (c : k) (hc : c ≠ 0)
    (M : Matrix (Fin n) (Fin n) k) (x : k) :
    (c • M).charpoly.IsRoot (c * x) ↔ M.charpoly.IsRoot x := by
  have h : Matrix.scalar (Fin n) (c * x) - c • M = c • (Matrix.scalar (Fin n) x - M) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij, mul_sub]
  rw [Polynomial.IsRoot.def, Polynomial.IsRoot.def, Matrix.eval_charpoly, Matrix.eval_charpoly, h,
    Matrix.det_smul]
  simp [hc]

private theorem ratio_smul {k : Type} [Field k] {n : ℕ} (ι : k ≃+* ℂ) (c : k) (hc0 : c ≠ 0)
    (M : Matrix (Fin n) (Fin n) k) (q : ℂ)
    (h : ∀ α : ℂ, (M.charpoly.map ι.toRingHom).IsRoot α →
      ¬ (M.charpoly.map ι.toRingHom).IsRoot (q * α)) :
    ∀ α : ℂ, ((c • M).charpoly.map ι.toRingHom).IsRoot α →
      ¬ ((c • M).charpoly.map ι.toRingHom).IsRoot (q * α) := by
  have key : ∀ y : ℂ, ((c • M).charpoly.map ι.toRingHom).IsRoot (ι c * y) ↔
      (M.charpoly.map ι.toRingHom).IsRoot y := by
    intro y
    obtain ⟨x, rfl⟩ := ι.surjective y
    rw [← map_mul, isRoot_map_equiv, isRoot_map_equiv, isRoot_charpoly_smul c hc0]
  intro α hα hβ
  have hιc : ι c ≠ 0 := (map_ne_zero_iff ι ι.injective).2 hc0
  have hα' : ι c * ((ι c)⁻¹ * α) = α := by field_simp
  have h1 : (M.charpoly.map ι.toRingHom).IsRoot ((ι c)⁻¹ * α) := by
    rw [← key, hα']
    exact hα
  refine h _ h1 ?_
  rw [← key]
  have h2 : ι c * (q * ((ι c)⁻¹ * α)) = q * α := by
    field_simp
  rw [h2]
  exact hβ
