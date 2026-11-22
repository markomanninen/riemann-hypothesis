module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformisationDataBeforeChoiceStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataFunctionalEquationDegreeOnStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifAssembly

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_degData_unif : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → Laws2 → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), U.LG = s.P.L ∧ U.gen = s.gen ∧ HEq U.cubG s.P.c :=
  fun h0 h1 h2 => GlobalTheory.UU.unif_assembly h1 h2 (GlobalTheory.T.exists_uniformisation_data_before_choice h0 h1) (GlobalTheory.T.exists_degenerationData_functionalEquation_degree_one h1 h2)

end GlobalTheory.UU
