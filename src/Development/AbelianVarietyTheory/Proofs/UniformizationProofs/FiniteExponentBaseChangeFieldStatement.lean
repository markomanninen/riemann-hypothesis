module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteExponentBaseChangeField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_exponent_base_change_field : GlobalFnsSt → AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ k : ℕ, U.FE (Kbar V) k → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F], U.FE F k := by
  first | exact @GlobalTheory.UU.FEDesc.fe_of_fe_kbar | exact GlobalTheory.UU.FEDesc.fe_of_fe_kbar | (intros; apply GlobalTheory.UU.FEDesc.fe_of_fe_kbar <;> assumption)
