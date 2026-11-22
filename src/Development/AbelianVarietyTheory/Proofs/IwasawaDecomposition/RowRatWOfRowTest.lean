module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff

@[expose] public section

open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem rowRatW_of_rowTest :
    (AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) → RowRatW :=
  by
    intro H
    have h := (StepW.of_all fun _ _ _ _ _ _ _ s => s.1 : StepW Start Pinned).trans H
    apply h.trans
    apply StepW.of_all
    intro K B f T w hK hF G Z hX Wt z a b _ c d _ _ _ _
    exact G Z hX Wt z a b c d

end GlobalTheory.Mem.LiteralAutomorphy
