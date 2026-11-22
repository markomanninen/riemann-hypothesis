module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealTopPowerSeriesLog
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueMapOfContinuousEvaluatioStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicEvaluationSubstCompatibleThickeningStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueSubMemPdIdealStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diffCoeffsInIdeal_top_powerSeries_log : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q], DIn (⊤ : Ideal B) (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  first | exact @GlobalTheory.QLog.LogDiff.dIn_log | exact GlobalTheory.QLog.LogDiff.dIn_log | (intros; apply GlobalTheory.QLog.LogDiff.dIn_log <;> assumption)
