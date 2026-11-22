module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
public import Mathlib
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepIndexLeS
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrXLeKOOfPrCat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOpenMirabolicProjectionToGL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeMeasureValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeConjugate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeIndexStep
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeIndexValue
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSubgroupAtPlace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelaxMemSupStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelaxPhiMemKOStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhiMemHStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HLeKOStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemLevelStatement

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped Pointwise in
theorem GlobalTheory.LevProd.level_eq_up_inf_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj ∧ ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hT' j hj t J hJ α g
  have hle : ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j),
      _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α ≤ _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J' j hj α' := by
    intro t J hJ α t' J' hJ' α' x hx
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨_root_.GlobalTheory.T.true_geometry_lattice_index_value_alt W hW u a ha hT' j hj t J hJ α t' J' hJ' α' x hx, ?_⟩, ?_⟩
    · exact (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2
    · exact (Subgroup.mem_pi _).2 fun i _ => _root_.GlobalTheory.T.true_geometry_lattice_index_step_alt W hW u a ha hT' j hj t J hJ α t' J' hJ' x hx i
  have hUp : _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj = _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α := by
    have hex : ∃ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads ∧ Nonempty (J.Ch j) := ⟨t, J, hJ, ⟨α⟩⟩
    unfold _root_.GlobalTheory.LevProd.upperLevelSubgroup
    rw [dite_eq_left hex]
    exact le_antisymm (hle _ _ hex.choose_spec.choose_spec.1 _ _ _ hJ α) (hle _ _ hJ α _ _ hex.choose_spec.choose_spec.1 _)
  rw [hUp]
  have hN : (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J)).Normal := by
    unfold GlobalTheory.FinPl.grpAt GlobalTheory.FinPl.congGrp; exact MonoidHom.normal_ker _
  constructor
  · intro hg
    have hf := _root_.GlobalTheory.T.true_geometry_lattice_measure_value_alt W hW u a ha hT' j hj t J hJ α g hg
    refine ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left hg, ?_⟩, ?_⟩, hf⟩
    · exact ((hJ.is.U j (by omega) _ g).1 hg).1
    · exact (Subgroup.mem_pi _).2 fun i _ => _root_.GlobalTheory.T.true_geometry_lattice_measure_step_alt W hW u a ha hT' j hj t J hJ α i (hf i)
  · rintro ⟨hr, hH⟩
    have hs := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hr).1).1
    have : g ∈ ((J.A.U j (J.ι j α) : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) * (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J) : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)))) := by
      rw [← Subgroup.mul_normal]; exact hs
    obtain ⟨x, hx, n, hn, rfl⟩ := this
    have hn' : n ∈ J.A.U j (J.ι j α) := by
      refine _root_.GlobalTheory.T.true_geometry_lattice_conjugate_alt W hW u a ha hT' j hj t J hJ α n hn fun i => ?_
      have h1 := _root_.GlobalTheory.T.true_geometry_lattice_measure_value_alt W hW u a ha hT' j hj t J hJ α x hx i
      have h2 := hH i
      rw [map_mul, Pi.mul_apply] at h2
      simpa using (Subgroup.mul_mem_cancel_left _ h1).1 h2
    exact mul_mem hx hn'
end
