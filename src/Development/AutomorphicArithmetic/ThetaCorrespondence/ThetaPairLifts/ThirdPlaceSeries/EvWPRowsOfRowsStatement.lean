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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWPRowsOfRows

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_pDiv_ties_of_class_sum_pin : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (τ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 τ → AtAll _root_.GlobalTheory.Fc.Ind.DivisorPointSummands 𝒜 τ → Ind.EvW (fun D _ _ _ => Formalism.BasicNotions.GoodFTAll D) 𝒜 τ → AtAll (fun D O c (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) => GlobalTheory.ExportPin.ClassSumPin b.pt ∧ b.pt.CompatibilityConditions) 𝒜 τ → Ind.EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 τ := by
  first | exact @_root_.GlobalTheory.Fc.Ind.evW_pRows_of_rows_alt | exact _root_.GlobalTheory.Fc.Ind.evW_pRows_of_rows_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.evW_pRows_of_rows_alt <;> assumption)
end
