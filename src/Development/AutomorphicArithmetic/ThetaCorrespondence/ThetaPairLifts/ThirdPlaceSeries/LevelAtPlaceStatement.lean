module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjStabilizesFramedLatticeIffStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionConjugatedEqMovedFrameMatrixStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionBlockTriangularIffMemParahoricLevelStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelCharacterEqInvBlockDetStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionSmallIntegersInPrimeDenseStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTwistPlaceLevelSinglePlaceCharacterStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelAtPlace

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (_root_.GlobalTheory.Fam.chrK_alt W t)), (a.Q PP ⟨t, hP⟩).Res E.δ ((_root_.GlobalTheory.Fam.pk_z W).xiR t PP) → ∀ (j d : ℕ) (hd : j + d = (a.Q PP ⟨t, hP⟩).s + 1), j < (I.rec7 l Z).R.m → ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin d), ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j ∈ levS (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ↔ x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J) ∧ ∀ hx : x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J, Lev.levChi (Yc (I.rec7 l Z) j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j) = ((((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).lam ⟨x, hx⟩ : ℂ) := by
  exact @_root_.GlobalTheory.QLevMid.level_at_place_alt_alt
end
