module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataFunctionalEquationDegreeOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationData_functionalEquation_degree_one : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∃ (D' : DegData V (IsLocalRing.maximalIdeal V)) (U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A G), U'.P = U.P ∧ U'.gen = U.gen ∧ U'.FE (Kbar V) 1) := by
  first | exact @GlobalTheory.UU.exists_degData_fe_one | exact GlobalTheory.UU.exists_degData_fe_one | (intros; apply GlobalTheory.UU.exists_degData_fe_one <;> assumption)
