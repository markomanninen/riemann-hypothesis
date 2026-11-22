module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumCountBoundLargeData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfCountAtOf
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

@[expose] public section

open GlobalTheory.SumCount GlobalTheory.SumSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datumCountBound_largeData : GlobalTheory.SumCount.DataK := by
  first | exact @GlobalTheory.SumCount.DataCount.dataK | exact GlobalTheory.SumCount.DataCount.dataK | (intros; apply GlobalTheory.SumCount.DataCount.dataK <;> assumption)
