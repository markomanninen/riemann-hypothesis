module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLValueUpperBoundPermutedWeightsOfFE
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds

@[expose] public section

open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeLValue_upperBound_permutedWeights_of_FE : GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → FieldDat → LBound := by
  first | exact @GlobalTheory.SqTop.lBound_of | exact GlobalTheory.SqTop.lBound_of | (intros; apply GlobalTheory.SqTop.lBound_of <;> assumption)
