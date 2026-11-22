module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDomainOfIsIntegrallyClosedOfIsReduced

@[expose] public section

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_of_isIntegrallyClosed_of_isReduced_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R], IsIntegrallyClosed R → IsDomain R := by
  first | exact @GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced | exact GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced | (intros; apply GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced <;> assumption)
