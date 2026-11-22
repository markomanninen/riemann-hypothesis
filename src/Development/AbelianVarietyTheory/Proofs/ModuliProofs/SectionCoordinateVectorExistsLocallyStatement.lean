module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinateVectorExistsLocally
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
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
theorem _root_.GlobalTheory.T.sectionCoordinateVector_exists_locally : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X), ∃ v, SecCoord M th x v) ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (p : Sp R), ∃ f : R, f ∉ p.asIdeal ∧ ∃ v, SecCoord M th (spMap (algebraMap R (Localization.Away f)) ≫ x) v) ∧ ∀ p : X, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (v : I → R), IsOpenImmersion x ∧ p ∈ Set.range x ∧ SecCoord M th x v := by
  first | exact @GlobalTheory.ZM.LocalCoord.secCoord_local | exact GlobalTheory.ZM.LocalCoord.secCoord_local | (intros; apply GlobalTheory.ZM.LocalCoord.secCoord_local <;> assumption)
