module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StarCharacterSquareEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSupportSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelReductionCriterion
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelGeneratedByLocalUnipotentsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelCharacterEqBesselCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainCommutationValid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTypePlacesOfLevCh
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselAdaptedTranslateLevel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralAdaptedElementProperty
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Placed
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedBy
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowCharacterEqExtension

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_adapted_element_value_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ : GA D (D.sp.X 0), IsTransportAdelicCorrection (W.S.tr u) a₀ → ∀ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) → _root_.GlobalTheory.LevZero.StabiliserCondition f B a₀ a → ∀ κ : GA D (D.sp.Y 0), κ ∈ GfC (D.sp.Y 0) → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) → Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ) ∈ (_root_.GlobalTheory.LevZero.datZero_alt W).P.H → κ ∈ rowJ W.S.X W.Q.instEq → rowChi W.S.X W.Q.instEq κ = ((Formalism.L2.DIV.ext1 (_root_.GlobalTheory.LevZero.datZero_alt W).P.H (_root_.GlobalTheory.LevZero.datZero_alt W).P.chi (Formalism.L2.DIV.rTup (F := D.host.F) (E := D.host.E) (_root_.GlobalTheory.LevZero.frameAtTranslate f B a₀ a) (_root_.GlobalTheory.LevZero.datZero_alt W) (finE (D.sp.Y 0) κ)) : ℂˣ) : ℂ) := by
  first | exact @_root_.GlobalTheory.LevZeroChr.row_character_eq_extension_alt | exact _root_.GlobalTheory.LevZeroChr.row_character_eq_extension_alt | (intros; apply _root_.GlobalTheory.LevZeroChr.row_character_eq_extension_alt <;> assumption)
end
