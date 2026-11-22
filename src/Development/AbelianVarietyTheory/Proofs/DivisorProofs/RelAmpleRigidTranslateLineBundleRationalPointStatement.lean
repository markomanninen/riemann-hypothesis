module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundles
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_rigidTranslateLineBundle_rationalPoint : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), L.IsLB → ∀ a : 𝟙_ (Over (Sp K)) ⟶ B, Out.RelAmple B L → Out.RelAmple B (GlobalTheory.RigidTranslate.rigTransl L a) := by
  first | exact @GlobalTheory.RigidTranslate.relAmple_rigTransl_point | exact GlobalTheory.RigidTranslate.relAmple_rigTransl_point | (intros; apply GlobalTheory.RigidTranslate.relAmple_rigTransl_point <;> assumption)
