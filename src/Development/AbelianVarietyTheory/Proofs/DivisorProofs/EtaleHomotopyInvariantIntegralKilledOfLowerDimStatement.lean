module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantIntegralKilledOfLowerDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInvOfDirectedUnionStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariant_integral_killed_of_lowerDim : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ (E : Type) [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (s : D), s ≠ 0 → algebraMap D E s = 0 → HInv q E := by
  first | (exact @GlobalTheory.hInv_of_integral_killed_of_lower) | (exact GlobalTheory.hInv_of_integral_killed_of_lower) | (intros; apply GlobalTheory.hInv_of_integral_killed_of_lower  <;> assumption)
