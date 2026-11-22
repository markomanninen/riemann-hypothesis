module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepBeforeLastEqSSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelLeCompact
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FixLevCompactOpen
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeClosed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeFinal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelStep
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOfEachPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLSplitPlaceOfCarriesLatticeCompletio
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTupleFreeValue
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepBeforeLastEqSSucc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupleFreeLevelLeCompact
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsCompactTupleFreeLevelStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupleFreeLevelMovesStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemTupleFreeLevelOfMemKStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelIffRelaxStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelaxedLevelEqTupleFreeStatement

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
theorem GlobalTheory.PenLev.levels_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∃ U0 : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), U0 ≤ GfC _ ∧ IsCompact (U0 : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → (∀ g ∈ U0, GlobalTheory.FinPl.Moves _ g (a.g.x j).L (a.g.x j).L (_root_.GlobalTheory.PenBridge.finitePlaceCondition J)) ∧ (∀ κ, GlobalTheory.FinPl.InK _ (a.g.x j).L (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) κ → κ ∈ U0) ∧ ∀ α, ∃ c : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k, (∀ i, c i ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J) ∧ ∀ g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ U0 ∧ ∀ i, c i * _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i * (c i)⁻¹ ∈ GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J (GlobalTheory.StepData.box _ ((J.G i).ϖ ^ (J.E i).M)) ((J.E i).cos (cast (congrArg (J.E i).Ch (show j = (J.G i).s + 1 by
    have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
    exact Nat.add_right_cancel (hj.trans hs.symm))) (α i))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hA j hj
  have hcompact := _root_.GlobalTheory.PenLev.isCompact_baseLevelSubgroup W hW u a ha hA j hj
  refine ⟨_root_.GlobalTheory.PenLev.baseLevelSubgroup a j hj,
    _root_.GlobalTheory.PenLev.base_level_subgroup_le_gfc a j hj, hcompact, ?_⟩
  intro t J hJ
  have hmoves := _root_.GlobalTheory.PenLev.tuple_free_level_moves_alt W hW u a ha hA j hj t J hJ
  have hmemK := _root_.GlobalTheory.PenLev.mem_tuple_free_level_of_mem_K_alt W hW u a ha hA j hj t J hJ
  refine ⟨hmoves, hmemK, ?_⟩
  intro α
  have hlevel := _root_.GlobalTheory.PenLoc.level_iff_relax_alt W hW u a ha hA j hj t J hJ α
  obtain ⟨c, hc, hmem⟩ := hlevel
  refine ⟨c, hc, fun g => ?_⟩
  rw [hmem g, _root_.GlobalTheory.T.true_geometry_tuple_free_relation_alt W hW u a ha hA j hj t J hJ α]
end
