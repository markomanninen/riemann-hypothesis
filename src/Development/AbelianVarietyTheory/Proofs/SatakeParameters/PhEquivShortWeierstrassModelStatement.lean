module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhEquivShortWeierstrassModel
public import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phEquiv_shortWeierstrassModel : Formalism.L2.KerInert.BeCob.PhTie := by
  first | exact @GlobalTheory.ShortModelTie.phTie | exact GlobalTheory.ShortModelTie.phTie | (intros; apply GlobalTheory.ShortModelTie.phTie <;> assumption)
