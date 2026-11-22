module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitSubtorusOfIdempotentFamily
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_subtorus_of_idempotent_family : GlobalTheory.RegSS.SubtorusOfIdempotents := by
  first | exact @GlobalTheory.RegSS.IdemTorus.subtorusOfIdempotents | exact GlobalTheory.RegSS.IdemTorus.subtorusOfIdempotents | (intros; apply GlobalTheory.RegSS.IdemTorus.subtorusOfIdempotents <;> assumption)
