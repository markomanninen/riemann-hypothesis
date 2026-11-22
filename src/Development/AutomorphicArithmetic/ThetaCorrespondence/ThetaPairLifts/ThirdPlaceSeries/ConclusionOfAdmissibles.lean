module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Formalism.SharpRestriction.LevelLetterCocycles.TypePrimeCongruences
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralElementsFromIdempotentCoeffsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualFamiliesContinuousStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeCompletionDegreeOneCountProofStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalOfArtinReciprocity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCharactersTypePrimeProofStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMemAdjoin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpRangePositiveSignPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualJumpRangeNegativeSignPlaceProofStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftFMonoLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountDirectLiftingProofStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountDualLiftingProofStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeFamilyPotentiallyCrystallineCommonTameExtensStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SecondClosedOfFirstClosed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedGaloisRepCharacterBlocksStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeLocalGlobal
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeE
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocus
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosingAtRecord
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodParIffGoodSig
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisation
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitLeOfFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatPowSubOneLe
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsNoCut
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsNoCutOfArtinStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CongruenceAtTypePrimes
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CutBoundOfSteps
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BcAllStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePrimeBoundOfEtaBound

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
namespace GlobalTheory
theorem conclusion_of_typeLocus_alt {D : D7} (P : Pend D) (CT : ℕ)
    (hcut : ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ π ∈ D.nd.Zgood i,
      ∃ (Xs : Set (D.nd.X i)) (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i),
        CutAt i k π Xs β b ∧ TypeLocus P i k Xs)
    (hl5 : _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT fun i k ρ eta => ∀ π ∈ D.nd.Zgood i, ∀ Xs : Set (D.nd.X i), π ∈ Xs →
      TypeLocus P i k Xs → LocalCongruenceBound CT eta i ρ π (vccCut i Xs π)) :
    _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (CongruenceLocalDecomposition CT) := by
  intro i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3 h4 h5 h7 h8
  have hQ := hl5 i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3 h4 h5 h7 h8
  have hc := hcut i k hl
  choose! Xs β b hcb using hc
  refine ⟨Xs, β, b, fun π hπ => ⟨(hcb π hπ).1, ?_⟩⟩
  exact hQ π hπ (Xs π) (hcb π hπ).1.1 (hcb π hπ).2
theorem admT_of_adm5_eigSpan_tieInePoly : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (P : Pend D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) (CT : ℕ), 8 * (CT : ℝ) ≤ C → SumRepresentations.adm5 D → EigSpan P → TieInePoly D → admT (D := D) CT → LocalPushoutProposition (D := D) → ResidualAbsIrreducible (D := D) → TypePrimeChoiceLemmas (D := D) → admDZ P → _root_.Formalism.MainNotions.PairedCharacterCondition.GaloisFamilyConditions' (D := D) → admG5 (D := D) → admG6 (D := D) → GlobalTheory.TypeLeaf.SerLoc D → admTB (D := D) HW F → admBK (D := D) → admBC (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.LocalGlobalCompatibility' (D := D) → SumRepresentations.tie0 D → tieChi (D := D) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) C CT := by
  intro hGAR D P HW F C CT hC hadm5 hEig hTie hT hLOC hRbar hN5g hDZ hG14 hG5 hG6 hSer hTB hBK hBC hLGC htie0 htieChi
  have hSteps : _root_.GlobalTheory.Pass.NoCutStatement := _root_.GlobalTheory.Pass.stepsNoCut_of_artin_alt hGAR
  have hCent : CentralElt D := hSteps.2.1 hSteps.1 D P
  have hl5 := _root_.GlobalTheory.Pass.cutBound_of_steps_alt hSteps D P HW F CT hadm5 (GlobalTheory.Per.ResFinite.adm12_elementDenominator D) hTie hT hLOC hRbar hN5g hDZ hG14 hG5 hG6 hTB
    hBK hBC hLGC (GlobalTheory.FontaineAdmissible.fontaineProperties_all_places D) htie0 htieChi
  have hcut := _root_.GlobalTheory.T.admBC_of_serLoc D P hSer hBC hLGC htie0 hadm5 hEig hCent
  have h3 : _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (CongruenceLocalDecomposition CT) := _root_.GlobalTheory.conclusion_of_typeLocus_alt P CT hcut hl5
  have h4 : _root_.Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.CongruenceAtTypePrimes' (D := D) CT (EtaBound CT) := by
    intro i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3' h4 h5 h7 h8
    exact GlobalTheory.EtaFromCut.etaBound_of_cut D CT i k ρ eta
      (h3 i k k' hkk' hl r ρ hr hdec eta s S sg U h1 h2 h3' h4 h5 h7 h8)
  exact _root_.GlobalTheory.typePrimeBound_of_etaBound_alt D C CT hC h4
end GlobalTheory
end
