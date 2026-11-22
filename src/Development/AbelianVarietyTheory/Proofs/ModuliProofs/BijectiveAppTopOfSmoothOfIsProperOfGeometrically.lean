module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), Smooth p → IsProper p →
      GeometricallyConnected p → Function.Bijective p.appTop.hom := by
  intro K _ X p hs hp hg

  haveI := hs
  haveI := hp
  haveI := hg
  haveI : GeometricallyIntegral p :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected X _ p hs hg
  haveI : IsIso p.appTop := ProperFunctions.isIso_appTop_of_field p
  exact ConcreteCategory.bijective_of_isIso p.appTop

end GlobalTheory
