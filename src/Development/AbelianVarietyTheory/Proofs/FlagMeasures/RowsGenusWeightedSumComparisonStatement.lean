module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsGenusWeightedSumComparison
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowsGenus_weightedSumComparison : GlobalTheory.TypeAsm.RowsOrbC := by
  first | exact @GlobalTheory.RowsOrb.rowsOrbC | exact GlobalTheory.RowsOrb.rowsOrbC | (intros; apply GlobalTheory.RowsOrb.rowsOrbC <;> assumption)
