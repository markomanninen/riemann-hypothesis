module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBase
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQProjOver_comp_of_isFinite_noetherianBase : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) (f : X ⟶ Y) (s : Y ⟶ Sp R), IsFinite f → IsQProjOver s → IsQProjOver (f ≫ s) := by
  first | exact @GlobalTheory.isQProjOver_comp_of_isFinite_noetherian | exact GlobalTheory.isQProjOver_comp_of_isFinite_noetherian | (intros; apply GlobalTheory.isQProjOver_comp_of_isFinite_noetherian <;> assumption)
