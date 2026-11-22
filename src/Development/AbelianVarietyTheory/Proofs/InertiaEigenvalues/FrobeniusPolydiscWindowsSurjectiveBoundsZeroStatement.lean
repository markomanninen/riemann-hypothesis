module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPolydiscWindowsSurjectiveBoundsZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm

@[expose] public section

open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_polydisc_windows_surjective_bounds_zero : WinThm := by
  first | exact @GlobalTheory.PMonE.winThm | exact GlobalTheory.PMonE.winThm | (intros; apply GlobalTheory.PMonE.winThm <;> assumption)
