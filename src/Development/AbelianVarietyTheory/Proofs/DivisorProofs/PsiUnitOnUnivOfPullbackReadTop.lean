module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricDataComparePolarisedUpToFunction
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioDescendsDegenerationPsiFamily
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LiftThreeOverMapComp
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSectionOfTransversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescalePsiEvenTauBimultIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomEvenDefectBimultiplicativePeriods
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.EqZeroIffSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickening
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackKernelBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothProjOfFree
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAffineWeightUnits
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PreimageEqTopOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InhabitedAndRefines
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitValEqMul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiScalarsRelationsUpToBaseUnits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFreeAbelianIsCoboundary
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullTopUnit
open GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

theorem psiUnitOn_pull_top {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') (hW : hD.W = ⊤) (x : D'.X) :
    PsiUnitOn D' x Set.univ := by
  have hI : IsIso hD.W.ι := by rw [hW, ← Scheme.topIso_hom]; infer_instance
  let h : Sp R' ⟶ (TW hD.W).left := specOf φ ≫ inv hD.W.ι
  have hh : h ≫ hD.W.ι = specOf φ := by simp [h]
  have hg : hD.g = jK R' ≫ h := by
    rw [← cancel_mono hD.W.ι, hD.g_comm, Category.assoc, hh]
  have sq : (D'.c x).left ≫ proj hD = h ≫ (toUnit (TW hD.W) ≫ D.c (hD.xe x)).left := by
    rw [hD.c_pr x, ← hh, Category.assoc]; rfl
  obtain ⟨a, ha, va⟩ := exists_down_om hD.w_gen D.P.isLB D'.P.isLB (Y' := Sp R') (K := PUnit)
    (φ' := fun _ => (D'.c x).left) h (fun _ => sq) (hD.psiW.psi (hD.xe x)) (hD.psiW.psi_gen _)
  refine (psiUnitOn_univ_iff D' x).2 ⟨a, ha, corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
  have e₁ := PsiEvenPull.psi_pull hD x (𝟙 _) y hJ hJ'
  have e₂ := va _ (𝟙 _ ≫ jK R') y J J' hJ hJ'
  rw [Fintype.prod_unique, zpow_neg_one, Category.assoc (𝟙 _) (jK R') h, ← hg] at e₂
  have e := e₁.symm.trans e₂
  exact (val_pull hJ' _ _ _).trans (mul_left_cancel e).symm

end GlobalTheory.PullTopUnit
