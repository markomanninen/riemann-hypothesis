module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmValuesExponentLogSumLe
public import Formalism.PairingDivisors.StatementN

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmValues_exponent_log_sum_le : Formalism.PairingDivisionLocalBalance.CESum := by
  first | exact @GlobalTheory.dividedPowerValuations_cESum | exact GlobalTheory.dividedPowerValuations_cESum | (intros; apply GlobalTheory.dividedPowerValuations_cESum <;> assumption)
