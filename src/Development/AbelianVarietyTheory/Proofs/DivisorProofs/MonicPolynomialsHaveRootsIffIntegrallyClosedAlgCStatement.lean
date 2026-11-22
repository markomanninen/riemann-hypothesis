module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIffIntegrallyClosedAlgC
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed : ∀ (D : Type) [CommRing D] [IsDomain D], AIC D ↔ (IsIntegrallyClosed D ∧ IsAlgClosed (FractionRing D)) := by
  first | (exact @GlobalTheory.AICIff.aic_iff) | (exact GlobalTheory.AICIff.aic_iff) | (intros; apply GlobalTheory.AICIff.aic_iff  <;> assumption)
