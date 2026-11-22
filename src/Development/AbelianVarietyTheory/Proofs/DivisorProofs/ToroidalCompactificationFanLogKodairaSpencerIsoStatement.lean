module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationFanLogKodairaSpencerIso
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidalCompactificationFan_logKodairaSpencer_iso : GlobalTheory.Published.ToroidalForFanKS := by
  first | exact @GlobalTheory.TorKSField.toroidalForFanKS | exact GlobalTheory.TorKSField.toroidalForFanKS | (intros; apply GlobalTheory.TorKSField.toroidalForFanKS <;> assumption)
