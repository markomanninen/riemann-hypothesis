module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
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
theorem _root_.GlobalTheory.T.thetaLevelPullback_id_comp_cancel : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (s'' : S'' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (t'' : TObj g k J b s''), TMap t t (𝟙 S) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S'), TMap t' t f → (TMap t'' t' f' ↔ TMap t'' t (f' ≫ f)) := by
  first | exact @GlobalTheory.ZM.tmap_id_comp_cancel | exact GlobalTheory.ZM.tmap_id_comp_cancel | (intros; apply GlobalTheory.ZM.tmap_id_comp_cancel <;> assumption)
