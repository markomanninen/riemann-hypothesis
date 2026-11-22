module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCover
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
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_descends_etale_cover : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp K) (d : ℕ), Etale π → Surjective π → LocallyOfFiniteType s → SmoothOfRelativeDimension d (π ≫ s) → SmoothOfRelativeDimension d s := by
  first | exact @GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover | exact GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover | (intros; apply GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover <;> assumption)
