module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.PullPar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.IndInf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalTwists.Reduce
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.CentChar
public import GroundTheory.AutomorphicForms.ReductionIdele
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AbsExpo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsGalRepOfOfIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusSignCompatibility
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Lit

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem norm_deg (w : HeightOneSpectrum (𝓞 E)) :
    normV w = normV (w.under (𝓞 F)) ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 F)).isMaximal
  have hnorm : ∀ {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)),
      normV v = Ideal.absNorm v.asIdeal := by
    intro L _ _ v
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hnorm, hnorm]
  exact (Ideal.absNorm_pow_inertiaDeg (w.under (𝓞 F)).asIdeal w.asIdeal).symm

private theorem deg_sum (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F))
    (T : Finset (v.asIdeal.primesOver (𝓞 E))) : ∑ q ∈ T, q.1.inertiaDeg (𝓞 F) ≤ 2 := by
  have := v.isMaximal
  have : Fintype (v.asIdeal.primesOver (𝓞 E)) := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).fintype
  rw [← h2, Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]
  refine (Finset.sum_le_sum_of_subset T.subset_univ).trans (Finset.sum_le_sum fun q _ => ?_)
  have := q.2.1
  exact Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos _ _)

private theorem norm_split (h2 : Module.finrank F E = 2) {w w' : HeightOneSpectrum (𝓞 E)} (hne : w' ≠ w)
    (hu : w'.under (𝓞 F) = w.under (𝓞 F)) : normV w = normV (w.under (𝓞 F)) := by
  classical
  have := w.isPrime
  have := w'.isPrime
  have hu' : (w.under (𝓞 F)).asIdeal = w'.asIdeal.under (𝓞 F) := (congrArg HeightOneSpectrum.asIdeal hu).symm
  have hs := deg_sum h2 (w.under (𝓞 F)) {⟨w'.asIdeal, w'.isPrime, ⟨hu'⟩⟩, ⟨w.asIdeal, w.isPrime, ⟨rfl⟩⟩}
  rw [Finset.sum_pair fun h => hne (HeightOneSpectrum.ext (congrArg Subtype.val h))] at hs
  have h3 := w.asIdeal.inertiaDeg_pos (𝓞 F)
  have h4 := w'.asIdeal.inertiaDeg_pos (𝓞 F)
  rw [norm_deg (F := F) w, show w.asIdeal.inertiaDeg (𝓞 F) = 1 by dsimp only at hs; omega, pow_one]

private theorem gal_two (h2 : Module.finrank F E = 2) : ∃ σ : E ≃ₐ[F] E, σ ≠ 1 ∧ ∀ τ : E ≃ₐ[F] E, τ = 1 ∨ τ = σ := by
  have : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, hy, hy'⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  exact ⟨y, hy, fun τ => (em (τ = 1)).imp_right (hy' τ)⟩

end Places

section Main

variable {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyReal E] [Algebra F E] {a : ℕ}

variable (F) in
private def Concl (π : TR.CuspSub E a) : Prop :=
  ((∀ (v v' : InfinitePlace E) (m : Multiset ℂ), v.comap (algebraMap F E) = v'.comap (algebraMap F E) →
      π.HasInfChar v m → π.HasInfChar v' m) ∧
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) →
      ∃ B, π.HasSat w B ∧ π.HasSat w' B) ∨
  ∃ P : TR.CuspSub F (2 * a),
    (∀ (v v' : InfinitePlace E) (m m' : Multiset ℂ), v ≠ v' → v.comap (algebraMap F E) = v'.comap (algebraMap F E) →
      π.HasInfChar v m → π.HasInfChar v' m' → P.HasInfChar (v.comap (algebraMap F E)) (m + m')) ∧
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      (∀ w' : HeightOneSpectrum (𝓞 E), w' ≠ w → w'.under (𝓞 F) = w.under (𝓞 F) →
        ∃ B B', π.HasSat w B ∧ π.HasSat w' B' ∧ P.HasSat (w.under (𝓞 F)) (B + B')) ∧
      (normV w = normV (w.under (𝓞 F)) ^ 2 → ∃ B B' : Multiset ℂˣ, π.HasSat w (B'.map (· ^ 2)) ∧
        B = B' + B'.map (fun b => -b) ∧ P.HasSat (w.under (𝓞 F)) B)

end Main
