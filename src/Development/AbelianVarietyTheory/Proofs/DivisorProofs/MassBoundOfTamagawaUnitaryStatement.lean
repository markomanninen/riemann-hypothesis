module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassBoundOfTamagawaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_bound_of_tamagawa_unitary : GlobalTheory.Published.TamagawaSpecialUnitary → GlobalTheory.UCls.MassBound := by
  first | exact @GlobalTheory.UCls.massBound_of_tamagawa | exact GlobalTheory.UCls.massBound_of_tamagawa | (intros; apply GlobalTheory.UCls.massBound_of_tamagawa <;> assumption)
