module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConsecutiveStep
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattices_consecutive_step : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j + 1 < D.R.m → ∀ (g : GA D (Yc D j)) (g' : GA D (Yc D (j + 1))), g ∈ GfC (Yc D j) → g' ∈ GfC (Yc D (j + 1)) → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M → IsSelfDualC (Yc D (j + 1)) M' → (∀ P, GlobalTheory.FinPl.Moves (Yc D j) g ((pk W).ΛY j) M P) → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g' ((pk W).ΛY (j + 1)) M' P) → (∀ P, ∀ x ∈ GinfC (Yc D j), ∀ x' ∈ GinfC (Yc D (j + 1)), GlobalTheory.FinPl.Vac (pk W).ψ (Yc D j) (Yc D (j + 1)) M M' (fun _ => True) ((pk W).ωY W.P.A3.A.μ0 j (x * g, x' * g') (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) P))) ∧ (pk W).ωY W.P.A3.A.μ0 j (g, g') (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((pk W).vac j) 1) ≠ 0 := by
  exact @GlobalTheory.StepMove.fock_vac_moved
