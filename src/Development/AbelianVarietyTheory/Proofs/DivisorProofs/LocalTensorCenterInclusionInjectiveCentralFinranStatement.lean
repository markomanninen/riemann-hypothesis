module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTensorCenterInclusionInjectiveCentralFinran
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntVZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralTensorPointsSharpStableRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupActionRingHom

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTensorCenterInclusion_injective_central_finrank : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Function.Injective (iotaF G v) ∧ (∀ z x, Commute (iotaF G v z) x) ∧ Module.finrank (Qv v) (Qv v ⊗[ℚ] G.C) = G.n ^ 2 * Module.finrank (Qv v) (Qv v ⊗[ℚ] G.F) := by
  first | (exact @GlobalTheory.OrbFinAf.iotaF_props) | (exact GlobalTheory.OrbFinAf.iotaF_props) | (intros; apply GlobalTheory.OrbFinAf.iotaF_props  <;> assumption)
