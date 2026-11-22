module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoopRowsOfLargeGapDiscreteSeries

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.ThmSOwn

theorem _root_.GlobalTheory.T.loopRows_of_large_gap_discreteSeries :
    GlobalTheory.GapIn.Hyp → Formalism.L2.SG.LocWSOf.BesselOfW → BpJoin.ThmBpDS →
    Formalism.L2.SG.Pf.WuDecayOfGap → Formalism.L2.SG.RowsDef.RowsFinDim →
    ∀ (𝒞 : FamClass) (sel : SSel 𝒞),
      (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) →
      (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) →
      LoopRowS 3 𝒞 sel :=
  GlobalTheory.LoopRowsCloseGap.loop_rows_closed_gap
