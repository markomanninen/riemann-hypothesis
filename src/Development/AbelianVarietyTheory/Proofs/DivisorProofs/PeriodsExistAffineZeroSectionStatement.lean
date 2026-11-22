module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsExistAffineZeroSection
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif

@[expose] public section

open GlobalTheory.AnPer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_exist_affine_zero_section : PExist := by
  first | exact @GlobalTheory.AnPer.periods_exist | exact GlobalTheory.AnPer.periods_exist | (intros; apply GlobalTheory.AnPer.periods_exist <;> assumption)
