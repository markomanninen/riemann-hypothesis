module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKTrivialOfPrincipalGenericFibreDvr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroupK_trivial_of_principal_genericFibre_dvr : Laws → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → RelAmple B M.L.L → KTriv B M.L.L := by
  first | exact @GlobalTheory.KTrivSpread.kTriv_of_generic_fibre | exact GlobalTheory.KTrivSpread.kTriv_of_generic_fibre | (intros; apply GlobalTheory.KTrivSpread.kTriv_of_generic_fibre <;> assumption)
