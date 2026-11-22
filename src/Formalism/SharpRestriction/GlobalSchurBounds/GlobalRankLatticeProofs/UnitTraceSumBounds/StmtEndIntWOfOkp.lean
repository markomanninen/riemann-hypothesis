module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EndIntWOf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WfSubst
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WfRing
public import Mathlib
public import Formalism.PeriodIntegrals.AddIntG
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittLogarithm
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittFrobeniusEnd

@[expose] public section

namespace Formalism.MainNotions.Ext

theorem substWf_holds : SubstWf :=
  fun p _ σ f a hf ha h0 => witt_substitution p σ f a hf (fun n => ⟨0, by rw [pow_zero, one_mul]; exact ha n⟩) h0

theorem coefWfRing_holds : CoefWfRing := witt_ring_structure

theorem endIntWG_holds : EndIntWG :=
  fun p _ g hOk hW α hα hI =>
    witt_frobenius_end p g.W g.wq g.ex hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2 hOk.2.1 hOk.2.2.1 hOk.2.2.2 α.1
      ⟨0, by simpa using witt_pairing p α hα⟩ hI

end Formalism.MainNotions.Ext
