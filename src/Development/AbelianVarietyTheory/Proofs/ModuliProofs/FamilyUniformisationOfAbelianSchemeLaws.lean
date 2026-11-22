module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ThetaUnifAVOfLaws
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUniformisationOfAbelianVarietyUniformisatiStatement

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem familyUnif_of_laws : Out.Laws → N1c := by
  intro hL
  have hU : ThetaUnifAV :=
    thetaUnifAV_of_laws (by cases hL; assumption) (by cases hL; assumption) (by cases hL; assumption)
      (by cases hL; assumption) (by cases hL; assumption)
  exact GlobalTheory.T.familyUniformisation_of_abelianVariety_uniformisation hU hL

end GlobalTheory
