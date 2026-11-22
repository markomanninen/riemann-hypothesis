module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPairValueLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSumsVanishOfTrivialFlags
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalCharacterIdealPowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrderPullbackAlongHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularElementsBoundedPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedCoordinatesPPowerDenominator

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.FinFix

theorem finite_den_bdd (N : ℕ) (hN : 0 < N) (R : ℝ) :
    {q : ℚ | (∃ k : ℤ, q * N = k) ∧ |(q : ℝ)| ≤ R}.Finite := by
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  refine ((Set.finite_Icc (-⌈R * N⌉) ⌈R * N⌉).image (fun k : ℤ => (k : ℚ) / N)).subset ?_
  rintro q ⟨⟨k, hk⟩, hR⟩
  refine ⟨k, ?_, ?_⟩
  · have hkR : |(k : ℝ)| ≤ R * N := by
      have : (k : ℝ) = (q : ℝ) * N := by exact_mod_cast hk.symm
      rw [this, abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg _)
    have h1 := abs_le.1 hkR
    constructor
    · have : -(R * N) ≤ (k : ℝ) := h1.1
      have h3 : (-⌈R * N⌉ : ℝ) ≤ k := by
        have := Int.le_ceil (R * N); push_cast; linarith
      exact_mod_cast h3
    · have h3 : (k : ℝ) ≤ ⌈R * N⌉ := le_trans h1.2 (Int.le_ceil _)
      exact_mod_cast h3
  · show (k : ℚ) / N = q
    rw [← hk]; field_simp

end GlobalTheory.FinFix
