module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsComplOpenImmersions
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
theorem _root_.GlobalTheory.T.isQProjOver_of_isCompl_openImmersions : ∀ (R : Type) [CommRing R] (X X₁ X₂ : Scheme.{0}) (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) (s : X ⟶ Sp R), IsOpenImmersion f₁ → IsOpenImmersion f₂ → IsCompl (Set.range f₁) (Set.range f₂) → IsQProjOver (f₁ ≫ s) → IsQProjOver (f₂ ≫ s) → IsQProjOver s := by
  first | exact @GlobalTheory.ProjSpace.isQProjOver_of_isCompl | exact GlobalTheory.ProjSpace.isQProjOver_of_isCompl | (intros; apply GlobalTheory.ProjSpace.isQProjOver_of_isCompl <;> assumption)
