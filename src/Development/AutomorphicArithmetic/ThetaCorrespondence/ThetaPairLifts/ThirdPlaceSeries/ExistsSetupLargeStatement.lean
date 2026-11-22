module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersOfLargeScale
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousComplementFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepsCuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiAtPsiAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAssembly
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualAbsIrredGoodPointOfResidualIrred
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistAnnihilatesSelmerGroupsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachFunctorComparisonOfBhattScholzeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialPrimesSmallAlongFamilyStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSetupLarge

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hubData_admJ_setup : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C C₂ : ℝ) (CT : ℕ), TwGood Fm → _root_.GlobalTheory.NLink.FactsFAlt Fm C CT → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ShaFinOdd (Fm.D x i) → ∀ exc : Finset ℕ, ∃ (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW) (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)), X.exc = exc ∧ _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt (Fm.L x i) ∧ _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ := by
  first | exact @_root_.GlobalTheory.NLink.exists_setup_large_alt | exact _root_.GlobalTheory.NLink.exists_setup_large_alt | (intros; apply _root_.GlobalTheory.NLink.exists_setup_large_alt <;> assumption)
end
