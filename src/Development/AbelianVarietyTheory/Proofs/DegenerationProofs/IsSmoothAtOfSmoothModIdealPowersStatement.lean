module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSmoothAtOfSmoothModIdealPowers
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothAt_of_smooth_mod_ideal_powers : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (C : Type) [CommRing C] [Algebra R C] [Algebra.FiniteType R C], (∀ e : ℕ, Algebra.Smooth (R ⧸ I ^ (e + 1)) (TensorProduct R (R ⧸ I ^ (e + 1)) C)) → ∀ (q : Ideal C) [q.IsPrime], q.comap (algebraMap R C) = IsLocalRing.maximalIdeal R → Algebra.IsSmoothAt R q := by
  first | exact @GlobalTheory.SmoothAdic.isSmoothAt_of_smooth_quotient_pow | exact GlobalTheory.SmoothAdic.isSmoothAt_of_smooth_quotient_pow | (intros; apply GlobalTheory.SmoothAdic.isSmoothAt_of_smooth_quotient_pow <;> assumption)
