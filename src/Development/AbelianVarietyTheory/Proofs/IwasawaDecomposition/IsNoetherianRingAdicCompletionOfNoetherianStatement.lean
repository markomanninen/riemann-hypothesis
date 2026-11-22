module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian

@[expose] public section

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNoetherianRing_adicCompletion_of_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsNoetherianRing (AdicCompletion I R) := by
  first | exact @GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion | exact GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion | (intros; apply GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion <;> assumption)
