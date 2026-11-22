module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelOfPrincipalisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ampleArithHilbertSamuel_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.HSNef.AmpleHS := by
  first | exact @GlobalTheory.HSNef.ampleHS_of_principalisation | exact GlobalTheory.HSNef.ampleHS_of_principalisation | (intros; apply GlobalTheory.HSNef.ampleHS_of_principalisation <;> assumption)
