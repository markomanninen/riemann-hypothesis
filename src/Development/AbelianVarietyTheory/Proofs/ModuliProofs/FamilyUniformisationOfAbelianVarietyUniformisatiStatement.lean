module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUniformisationOfAbelianVarietyUniformisati
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyUniformisation_of_abelianVariety_uniformisation : ThetaUnifAV → Out.Laws → N1c := by
  first | exact @GlobalTheory.familyUnif_of_thetaUnif | exact GlobalTheory.familyUnif_of_thetaUnif | (intros; apply GlobalTheory.familyUnif_of_thetaUnif <;> assumption)
