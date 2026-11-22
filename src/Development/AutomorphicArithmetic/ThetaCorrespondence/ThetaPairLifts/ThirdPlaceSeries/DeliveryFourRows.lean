module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinersAndLiftsExistAtChoicesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvInjOfIsModelsOfTie
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JEvExistsAndJEvBar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeoAct
public import Formalism.LocalToGlobal.IndefiniteReal.RealTB
public import Formalism.LocalToGlobal.IndefiniteReal.RealPins
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFramesNormalAtLevelPlacesOfCharFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisationStatement
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.LocalRingCardinality.DataTies
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIoExtensionOfWeakCharacterisationFramesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEveryEmbeddingThirdKind
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftRowFiresOfWeakCharacterisation
public import Formalism.LocalRingCardinality.NFLeTwoMulTSq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FireStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBOfDecayStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaFireRowRecTieStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FramesExOfRealisationStatement

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
namespace GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem atAll_fourRows' : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜),
      AtAll _root_.GlobalTheory.Fc.Ind.FiringPointSummands 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.summandRealBound 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.ThresholdPointSummands 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.FramePointSummands 𝒜 σ := by
  intro hDS hHC hRD hCW 𝒜 σ
  have hF : AtAll _root_.GlobalTheory.Fc.Ind.FiringPointSummands 𝒜 σ := fun Fm hc x hx i =>
    _root_.GlobalTheory.T.indefinite_scale_theta_equality_alt hDS hHC hRD hCW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B
  refine ⟨hF, fun Fm hc x hx i => ?_, fun Fm hc x hx i => ?_, fun Fm hc x hx i => ?_⟩
  · exact _root_.GlobalTheory.T.indefinite_scale_theta_bound_right_alt hRD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B (Fm.parT x hx i).nV_ge (hF Fm hc x hx i).1
  · exact _root_.GlobalTheory.T.indefinite_scale_theta_identity_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B.Q (σ Fm hc x hx i).Rr (hF Fm hc x hx i).1
  · exact _root_.GlobalTheory.T.framesEx_of_realPins_indefinite_scale _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B.Q (σ Fm hc x hx i).pins
end GlobalTheory.Fc.Ind
end
end
