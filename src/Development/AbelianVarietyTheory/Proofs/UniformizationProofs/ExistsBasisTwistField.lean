module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyLinearEquivOfRel

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_basis_twist_field : Laws → Laws2 → (∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ α : D.X, ∃ b : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)), ∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)), ∃! c : Fin (k ^ D.P.g) → F, ∀ j, s.f j = ∑ i, DegPre.constBF D F (c i) _ * (b i).f j) :=
  fun _ h₂ _ _ _ D F _ _ _ hk α =>
    GlobalTheory.FamDimension.exists_basis_famSec (D := D) (F := F) h₂.secTwist hk α

end GlobalTheory.UU
