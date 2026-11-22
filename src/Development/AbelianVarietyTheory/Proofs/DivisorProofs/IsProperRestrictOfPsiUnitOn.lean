module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRestrictOfSubsetAbLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectivePointsLargerFieldGalois
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullbackDegree.EpsPullbackFst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrCongrOfResidueFixedByDecompositionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingFixedFieldInertiaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerOfValuationRingFixedFieldInertiaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentIntegralStructureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionOfGenericFibreDvrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionFieldRingEquivEqUnitMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearSymmFixesUnitSectionGenericFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearModelFixesUnitSectionAbelianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralTwistedComparisonAtFixedSectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoConstOfGenericIsoDvrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGenIsoPullbackLineBundleZpowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmplePowerOfExtensionGenericFibreAbelianModeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleBasisSectionsAbelianSchemeOverDvrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsoLineBundleSectionsTransferStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixDescentUnramifiedDvrStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExtendsUnramifiedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfUnramifiedAbelianSchemeModelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedFieldPointOfFixedBySubgroupStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldValuationRingStrictlyHenselianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfManyRationalTorsionPointsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralExtIsAlgClosedResidueField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOneOfPowOfClosedPoint
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PtEqOfProportional
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section
namespace GlobalTheory.UnifProperChar
section Inertia

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.BXOf GlobalTheory.UnramTorsion

attribute [local instance] gtGroup

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

end Inertia

section Reduction

open GlobalTheory.Published GlobalTheory.Published.AbVarRed

end Reduction

theorem exists_dvr_centre (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) [I.IsPrime] :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : R →+* V),
      IsAlgClosed (ResidueField V) ∧ Function.Injective φ ∧ (maximalIdeal V).comap φ = I := by
  obtain ⟨V, _, _, _, φ, hφ, hc⟩ : ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (φ : R →+* V), Function.Injective φ ∧ (maximalIdeal V).comap φ = I := by
    rcases eq_or_ne I ⊥ with rfl | hI
    · let K := FractionRing R
      let φ : R →+* PowerSeries K := (PowerSeries.C (R := K)).comp (algebraMap R K)
      have hφ : Function.Injective φ := PowerSeries.C_injective.comp (IsFractionRing.injective R K)
      refine ⟨PowerSeries K, inferInstance, inferInstance, inferInstance, φ, hφ, ?_⟩
      refine eq_bot_iff.2 fun r hr => ?_
      rw [Ideal.mem_comap, PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton,
        PowerSeries.X_dvd_iff] at hr
      have : algebraMap R K r = 0 := by simpa [φ] using hr
      exact (Ideal.mem_bot).2 (IsFractionRing.injective R K (this.trans (map_zero _).symm))
    · obtain ⟨V, _, _, hV, -, φ, h1, h2⟩ :=
        exists_complete_discreteValuationRing_of_prime_lt ⊥ I (bot_lt_iff_ne_bot.2 hI)
      exact ⟨V, inferInstance, inferInstance, hV, φ, (RingHom.injective_iff_ker_eq_bot φ).2 h1, h2⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨V', _, _, _, _, h1, h2, -, h3⟩ := GlobalTheory.ClosedResidueExt.exists_unramified_ext V hπ
  refine ⟨V', inferInstance, inferInstance, inferInstance, (algebraMap V V').comp φ, h3, h1.comp hφ, ?_⟩
  rw [← Ideal.comap_comap, ← hc]
  congr 1
  exact eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (algebraMap_isIntegral_iff.mpr h2) (maximalIdeal V'))

end GlobalTheory.UnifProperChar
