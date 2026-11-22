module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleRationalPointsFiniteClosed
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGenThetaOfIsProjBy
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KernelFiniteFlatHolds

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelOfLineBundle_rationalPoints_finite_closed : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∃ S : Finset A.left, (∀ s ∈ S, IsClosed ({s} : Set A.left)) ∧ ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A, GlobalTheory.CechPic.lam (cls L hL) (toUnit A ≫ x) (𝟙 A) = 0 → x.left (IsLocalRing.closedPoint K) ∈ S := by
  first | exact @GlobalTheory.KLFinite.kl_finite | exact GlobalTheory.KLFinite.kl_finite | (intros; apply GlobalTheory.KLFinite.kl_finite <;> assumption)
