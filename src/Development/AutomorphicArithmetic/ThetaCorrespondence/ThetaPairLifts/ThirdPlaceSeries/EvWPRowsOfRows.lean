module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
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
public import Formalism.LocalRingCardinality.DataNChTie
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionFirst
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionSecond
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionThird
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideCardEqOfCoord
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeliveryFourRowsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PRowsOfPartsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PNmjOfPDivOfClassSumPinStatement

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.Ind
theorem evW_pRows_of_rows_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (τ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 τ → AtAll _root_.GlobalTheory.Fc.Ind.DivisorPointSummands 𝒜 τ → Ind.EvW (fun D _ _ _ => Formalism.BasicNotions.GoodFTAll D) 𝒜 τ → AtAll (fun D O c (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) => GlobalTheory.ExportPin.ClassSumPin b.pt ∧ b.pt.CompatibilityConditions) 𝒜 τ → Ind.EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 τ := by
  intro hDS hHC hCR hCW 𝒜 τ hPA hDiv hG hPin
  obtain ⟨hF, hRB, -, hFr⟩ := _root_.GlobalTheory.T.fire_realBound_thR_frames_at_all hDS hHC hCR hCW 𝒜 τ
  refine Formalism.MainNotions.Closed.imp hG ?_
  intro eps Fm CH _ h hc
  obtain ⟨x0, hx0⟩ := h hc
  refine ⟨x0, fun x hx h0 i => ?_⟩
  have ha := w3_a hc
  have hp := hPin Fm ha x hx i
  exact _root_.GlobalTheory.T.bundle_lines_of_primitive_frames_div_nmj _ _ _ _ (hF Fm ha x hx i) (hRB Fm ha x hx i) (hPA Fm ha x hx i) (hFr Fm ha x hx i)
    (hDiv Fm ha x hx i) (_root_.GlobalTheory.T.pNmj_of_pDiv_classSumPin _ _ _ _ (hDiv Fm ha x hx i) hp.1) (hx0 x hx h0 i) hp.2
end GlobalTheory.Fc.Ind
end
