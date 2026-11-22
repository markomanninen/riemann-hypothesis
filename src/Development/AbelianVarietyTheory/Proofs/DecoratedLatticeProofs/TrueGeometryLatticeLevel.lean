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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLocalGLEmbeddingSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeOpen

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevOnto

theorem list_prod_map_mulSingle {n : ℕ} {G : Fin n → Type*} [∀ i, Monoid (G i)] (x : ∀ i, G i) (k : Fin n) :
    ∀ l : List (Fin n), l.Nodup → ((l.map fun i => Pi.mulSingle i (x i) k).prod = if k ∈ l then x k else 1)
  | [], _ => by simp
  | b :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, list_prod_map_mulSingle x k l hl.2]
    by_cases hb : b = k
    · subst hb
      simp [hl.1]
    · rw [Pi.mulSingle_eq_of_ne (Ne.symm hb), one_mul]
      simp [List.mem_cons, Ne.symm hb]

theorem list_prod_mulSingle {n : ℕ} {G : Fin n → Type*} [∀ i, Monoid (G i)] (x : ∀ i, G i) :
    ((List.finRange n).map fun i => Pi.mulSingle i (x i)).prod = x := by
  funext k
  rw [Pi.list_prod_apply, List.map_map]
  have := list_prod_map_mulSingle x k (List.finRange n) (List.nodup_finRange n)
  simpa [Function.comp_def] using this

theorem map_pr_eq_one {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (V : HSp D) (g : GA D V)
    (hg : SuppAt q.e V g) (hv : q.v ≠ q'.v) : (mt V g).map q'.pr = 1 := by
  obtain ⟨ε, hε, hE⟩ := q.above
  obtain ⟨ε', hε', hE'⟩ := q'.above
  rw [GlobalTheory.SplitCut.eFin_of_placeIdem hε] at hE
  rw [GlobalTheory.SplitCut.eFin_of_placeIdem hε'] at hE'
  have hsp := q'.split
  have h0 : q'.e * (q.e + cA D q.e) = 0 := by
    have h1 : q'.e = q'.e * (q'.e + cA D q'.e) := by rw [mul_add, hsp.1, hsp.2.1, add_zero]
    rw [h1, mul_assoc, hE', hE, ← map_mul, GlobalTheory.LocWeil.PlaceIdem.eFin_mul_eFin _ (Ne.symm hv), map_zero, mul_zero]
  have hpr : q'.pr (q.e + cA D q.e) = 0 := by
    rw [← q'.pr_sec (q'.pr _), q'.sec_pr, h0, map_zero]
  ext a b
  rw [Matrix.map_apply]
  have h2 : mt V g a b = (mt V g - 1) a b + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) a b := by
    rw [Matrix.sub_apply, sub_add_cancel]
  rw [h2, map_add (f := _), ← hg a b, map_mul, hpr, zero_mul, zero_add]
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem locHom_eq_one {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {Y : Type} [Fintype Y] [DecidableEq Y]
    (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (V : HSp D) (F : Frame k' V.rank Y) (g : GA D V)
    (hg : SuppAt q.e V g) (hv : q.v ≠ q'.v) : GlobalTheory.LevIdx.locHom q' V F g = 1 := by
  refine ((GlobalTheory.LevIdx.eq_locHom_iff q' V F g 1).1 ?_).symm
  rw [map_pr_eq_one q q' V g hg hv, Units.val_one, Matrix.mul_one, F.βγ]

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u}

end GlobalTheory.LevOnto
end

namespace GlobalTheory.LevOnto
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u}

end GlobalTheory.LevOnto
