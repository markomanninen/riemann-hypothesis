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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetPointGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBlochKatoConditionOfWachModulesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LongOrbitsRowColengthInertLocalisationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowsCDRowConditionLocalBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProofStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysOnCondOfEveryDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamifiedCoefficientChainsPrvTwentyFiveStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBOfBlochKatoTateDualityEulerCStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatementsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEulerStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctConstituentsAfterExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondTBAtRange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AmbientH1fOfLocalFiniteness
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
public import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientExtensionDecomposition
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
public import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.InertPlacesGoodSet
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherBis

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adm_at_inert_of_range : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.InertK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admitted i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) (X.cB i) := by
  first | exact @_root_.GlobalTheory.NLink.InertStep.main_alt_alt | exact _root_.GlobalTheory.NLink.InertStep.main_alt_alt | (intros; apply _root_.GlobalTheory.NLink.InertStep.main_alt_alt <;> assumption)
end
