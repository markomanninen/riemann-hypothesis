module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullDegKeepsBimultActionPolarisationElement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullDeg_keeps_bimult_action_polarisationElement : ∀ {O : Type} [CommRing O] [StarRing O] {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] {θ₀ : W →+* V} {D₀ : DegPre W} [Module O D₀.X] (o₀ : D₀.OAct O) {D : DegPre V} [Module O D.X] (hD : IsPullDeg θ₀ D₀ D) (ob : D.P.OAct O), (∀ (a : O) y, hD.xe (a • y) = a • hD.xe y) → (∀ (a : O) y, D.c (a • y) = D.c y ≫ ob.act a) → (∀ a : O, (ob.act a).left ≫ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = (hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀)) ≫ (o₀.onB.act a).left) → D₀.TauBimult → ∀ w0 : O, TraceFormTwistIso D₀ o₀ w0 → D.TauBimult ∧ ∃ o : D.OAct O, o.onB = ob ∧ TraceFormTwistIso D o w0 := by
  first | exact @GlobalTheory.tauBimult_and_exists_oAct_of_pullDeg | exact GlobalTheory.tauBimult_and_exists_oAct_of_pullDeg | (intros; apply GlobalTheory.tauBimult_and_exists_oAct_of_pullDeg <;> assumption)
