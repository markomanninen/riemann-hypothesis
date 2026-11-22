module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompleteDVRPointGenericPoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_point_genericPoint : ∀ (Z : Scheme.{0}) [IsIntegral Z] (W : Type) [CommRing W] [IsDomain W] [CharZero W] (_ : Sp W ⟶ Z), ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R), GlobalTheory.LN.CDvr R ∧ ∃ χ : Sp R ⟶ Z, ∀ y, χ y = genericPoint Z := by
  first | exact @GlobalTheory.GenTrait.exists_trait_genericPoint | exact GlobalTheory.GenTrait.exists_trait_genericPoint | (intros; apply GlobalTheory.GenTrait.exists_trait_genericPoint <;> assumption)
