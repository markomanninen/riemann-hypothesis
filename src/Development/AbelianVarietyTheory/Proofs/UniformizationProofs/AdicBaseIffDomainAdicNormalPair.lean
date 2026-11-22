module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPowDeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DegCompare

open GlobalTheory.PsiInPull GlobalTheory.PsiInPow

section Generic

variable {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (z : Z)

variable {L : LB X} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)

end Generic

variable {R : Type} [CommRing R] [IsDomain R]

variable (D : DegPre R)

section Values

variable {D} {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ

theorem val_tau (a b : D.X) : val (D.tau a b) r z J =
    val (D.psi (a + b)) r z J * (val (D.psi a) r z J)⁻¹ * (val (D.psi b) r z J)⁻¹ * (val D.rigK r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem val_tau_symm (a b : D.X) : val (D.tau a b) r z J = val (D.tau b a) r z J := by
  rw [val_tau r hJ, val_tau r hJ, add_comm b a, mul_right_comm (val (D.psi (a + b)) _ z J)]

end Values

end GlobalTheory.DegCompare
