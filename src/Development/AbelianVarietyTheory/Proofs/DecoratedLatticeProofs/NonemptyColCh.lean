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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocFac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchAtType
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIffUpMemStdHom
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIntIn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoeLatFrameOfEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.Fam.TopLocFac


open Formalism.IndefR.Lev Formalism.IndefR.Mult in
theorem nonempty_rowCh {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (u : D.what₂.Word)
    (g : Geo D) (hψ : IsStdChar D R.ψ (-1)) (t : T) : Nonempty (RowCh R P u g t) :=
  ⟨{ vP := fun _ => 0, vT := fun _ _ => 0, sBF := fun _ _ _ => (GlobalTheory.Unf.Inhab.nonempty_stepBF hψ _ _).some,
     sFB := fun _ _ _ => (GlobalTheory.Unf.Inhab.nonempty_stepFB hψ _ _).some, io := fun _ => 0, ioT := fun _ _ => 0 }⟩

theorem nonempty_colCh {D : D7} (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) : Nonempty (ColCh u C) :=
  ⟨{ kom := fun _ => 1, Ch := fun _ => Unit, dd := fun _ _ _ => 0, e := fun _ _ => 0, eT := fun _ _ _ => 0,
     Ram := fun _ => Set.univ, S := fun _ => id, rd := fun _ _ _ _ _ => 0, cV := fun _ => 1, cK := fun _ => 1, cP := 1 }⟩

end GlobalTheory.Fam.TopLocFac
end
