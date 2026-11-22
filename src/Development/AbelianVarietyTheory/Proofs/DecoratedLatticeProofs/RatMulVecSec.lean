module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthDecSumLatticeSelfDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocalModelSliceSourceLine

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreFrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rat_mulVec_sec (q : SplitPt D k) {a b : ℕ} (Q : Matrix (Fin a) (Fin b) D.host.E) (w : Fin b → k) :
    rat Q *ᵥ (fun i => q.sec (w i)) =
      fun i => q.sec ((Q.map (GlobalTheory.SliceModel.prH (GlobalTheory.LocMod.ofSplit q)) *ᵥ w) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact GlobalTheory.SliceModel.ι_mul_left (GlobalTheory.LocMod.ofSplit q) (w j) (incA D (Q i j))

end GlobalTheory.CoreFrameLat
