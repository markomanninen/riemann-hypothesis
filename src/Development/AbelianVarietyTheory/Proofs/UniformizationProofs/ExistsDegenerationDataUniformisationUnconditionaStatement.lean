module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataUniformisationUnconditiona
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationData_uniformisation_unconditional : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), U.LG = s.P.L ∧ U.gen = s.gen ∧ HEq U.cubG s.P.c := by
  first | exact @GlobalTheory.UU.exists_degData_unif_unconditional | exact GlobalTheory.UU.exists_degData_unif_unconditional | (intros; apply GlobalTheory.UU.exists_degData_unif_unconditional <;> assumption)
