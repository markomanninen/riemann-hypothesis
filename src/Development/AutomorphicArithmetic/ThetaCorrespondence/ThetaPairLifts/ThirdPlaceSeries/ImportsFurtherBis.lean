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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SetPointGood
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClosingFamilyX
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLink.InertStep
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.InertK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admitted i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) (X.cB i) := by
  intro hP D L P nch HW F Cm X C₂ hS hC hconds2 hBCD i htw hg hR hin π hπ
  obtain ⟨hG1, hG2, hG3, hG4, hG5, hG5x, hG6, hBK, hCont, hSS, hDec, hEps, hTie, hShape, hFont, hH2, hCFT⟩ :=
    _root_.GlobalTheory.T.set_pt_of_setup_not_twisted hP D L P nch HW F Cm X C₂ hS i hg π hπ
  have hcB : ∀ i', GlobalTheory.HubLoc.cBnum (D.nd.l i') ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i' := by
    intro i'
    rw [hS.canon.cB]
    exact le_rfl
  have hX := _root_.GlobalTheory.closingFamilyX_alt_alt hP.font hP.fin D HW F L X (_root_.GlobalTheory.JumpStatement.holds_all_alt D)
    (hS.facts.admJ L hS.par) hS.par67 hS.facts.Conclusion1.1 hS.facts.large.2.1 hS.canon.fam hcB
  obtain ⟨M0, h0, hJ⟩ := hX.2.1 i hR π
  have hTB : TruncatedSeriesCountingIdentities.admTB i (X.r i) π (X.cB i) :=
    GlobalTheory.T.localBlochKatoCondition_of_wachModules D HW F i (X.r i) (X.ρ i) π M0 h0 (X.cB i)
      (GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler hP.bk hP.tate hP.euler D HW F Cm) (GlobalTheory.T.crystallineLatticeWachModuleExists_proof D HW F Cm) (GlobalTheory.crysOnCond_all D HW F) hFont hJ
  have h11 : 11 ≤ D.nd.l i := by
    have := D.nd.lPrime i
    exact GlobalTheory.Survey.InertPlacesGoodSet.eleven_le this.out hin (le_trans (by norm_num) hS.split)
  have hD := hS.canon.data
  have hROW : TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) := by
    by_cases hB : KillingConditions.IsRowB L (D.nd.l i)
    · rw [hD.rowB i hin hB]
      exact GlobalTheory.T.longOrbits_rowColength_inertLocalisation D L P HW C₂ i (X.r i) (X.ρ i) π (X.dc i) hconds2 hC hS.par67 h11
        ((hBCD i htw hin π hπ).1 hB)
    · have hband : X.band i = fun lam => bandOf L HW 320 i (X.r i) (X.ρ i) lam := by
        funext lam
        exact propext (hD.band i lam)
      rw [hD.rowCD i hin hB, hband]
      exact GlobalTheory.T.rowsCD_rowCondition_localBounds D L P HW F C₂ i (X.r i) (X.ρ i) π (X.dc i)
        (GlobalTheory.T.localLiftingTheoremB_of_blochKato_tateDuality_eulerChar hP.bk hP.tate hP.euler D HW F Cm 320 le_rfl)
        (GlobalTheory.T.prv_twenty_five_of_blochKato_tateDuality_eulerChar hP.bk hP.tate hP.euler D HW F Cm)
        (GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hP.bk hP.tate hP.euler D HW F Cm) hS.par67 h11 hπ ((hBCD i htw hin π hπ).2 hB)
  have hLIFT : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i (X.r i) (X.dc i) (X.e' i) := by
    intro w hw hwc
    rw [hD.col i hin] at hwc
    simp at hwc
  exact ⟨hG1, hG2, hG3, hG4, hG5, hG5x, hG6, hBK, hTB, hROW, hLIFT, hCont, hSS, hDec, hEps, hTie, hShape, hFont,
    hH2, hCFT⟩
end GlobalTheory.NLink.InertStep
end
