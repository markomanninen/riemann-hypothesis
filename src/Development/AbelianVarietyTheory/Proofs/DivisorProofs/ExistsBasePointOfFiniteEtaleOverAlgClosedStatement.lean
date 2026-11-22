module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasePointOfFiniteEtaleOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableExtensionMultiplesOfSemistable
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSubgroupEqRangeOfLists
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActDescendOfGenerators

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_point_of_finite_etale_over_algClosed : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (X : Scheme.{0}) (p : X ⟶ Sp k₀), IsFinite p → Etale p → ∀ x : Sp K ⟶ X, x ≫ p = spMap (algebraMap k₀ K) → ∃ x₀ : Sp k₀ ⟶ X, x₀ ≫ p = 𝟙 _ ∧ spMap (algebraMap k₀ K) ≫ x₀ = x := by
  first | exact @GlobalTheory.FinEtPoints.exists_point_of_finite_etale | exact GlobalTheory.FinEtPoints.exists_point_of_finite_etale | (intros; apply GlobalTheory.FinEtPoints.exists_point_of_finite_etale <;> assumption)
