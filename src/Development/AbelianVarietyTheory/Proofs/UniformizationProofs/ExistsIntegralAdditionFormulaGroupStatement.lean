module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralAdditionFormulaGroup
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
theorem _root_.GlobalTheory.T.exists_integral_addition_formula_group : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ : U.SecGT (𝟙_ _) 1, ∃ (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2), r ≠ 0 ∧ U.AddG θ r σ σ') := by
  first | exact @GlobalTheory.UU.exists_addG | exact GlobalTheory.UU.exists_addG | (intros; apply GlobalTheory.UU.exists_addG <;> assumption)
