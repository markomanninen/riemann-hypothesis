module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneToRootsOfUnitySectionsSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuValInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.MuTw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_surjective : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Surjective ((etaS q).hom.app (op U)).hom := by
  first | (exact @GlobalTheory.EtC.MuTw.etaS_surjective) | (exact GlobalTheory.EtC.MuTw.etaS_surjective) | (intros; apply GlobalTheory.EtC.MuTw.etaS_surjective  <;> assumption)
