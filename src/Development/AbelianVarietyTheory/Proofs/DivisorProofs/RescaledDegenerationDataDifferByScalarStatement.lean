module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaledDegenerationDataDifferByScalar
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
theorem _root_.GlobalTheory.T.rescaled_degenerationData_differ_by_scalar : ∀ {O : Type} [CommRing O] [StarRing O] {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module O Q.X] (oQ : Q.OAct O) (g : Q.X → (FractionRing V)ˣ) (o' : letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; (GlobalTheory.PolDeg.rescale Q g).OAct O), (letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; o'.onB = oQ.onB) → Q.TauBimult → (GlobalTheory.PolDeg.rescale Q g).TauBimult → ∀ w0 : O, TraceFormTwistIso Q oQ w0 → (letI : Module O (GlobalTheory.PolDeg.rescale Q g).X := ‹Module O Q.X›; TraceFormTwistIso (GlobalTheory.PolDeg.rescale Q g) o' w0) → ∃ q : Q.X → Q.X → (FractionRing V)ˣ, (∀ a b, q a b = q b a) ∧ (∀ a a' b, q (a + a') b = q a b * q a' b) ∧ (∀ (x : O) a b, q (x • a) b = q a (star x • b)) ∧ ∀ y, (g y)⁻¹ = q y (w0 • y) := by
  first | exact @GlobalTheory.RatioScalar.scalar | exact GlobalTheory.RatioScalar.scalar | (intros; apply GlobalTheory.RatioScalar.scalar <;> assumption)
