module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegrationOverCyclesHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif

@[expose] public section

open GlobalTheory.AnPer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integrationOverCyclesHom : PHom := by
  first | exact @GlobalTheory.AnPer.pHom | exact GlobalTheory.AnPer.pHom | (intros; apply GlobalTheory.AnPer.pHom <;> assumption)
