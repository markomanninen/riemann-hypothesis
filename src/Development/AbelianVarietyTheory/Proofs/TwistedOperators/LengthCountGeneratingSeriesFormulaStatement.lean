module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthCountGeneratingSeriesFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_count_generating_series_formula : GenFun := by
  first | exact @GlobalTheory.InertZeta.genFun_holds | exact GlobalTheory.InertZeta.genFun_holds | (intros; apply GlobalTheory.InertZeta.genFun_holds <;> assumption)
