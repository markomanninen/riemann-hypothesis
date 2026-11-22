module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceAbsolutelyIntegrallyClose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariance_absolutelyIntegrallyClosed : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T], AIC T → IsUnit (q : T) → HInv q T := by
  first | (exact @GlobalTheory.HInvAic.main) | (exact GlobalTheory.HInvAic.main) | (intros; apply GlobalTheory.HInvAic.main  <;> assumption)
