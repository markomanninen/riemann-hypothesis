module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.StatementTBB
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSidesStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentClosureStatement

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SupTau

theorem hsq_nonneg (r : ℕ) (T b : ℝ) : 0 ≤ Hsq r T b := by
  unfold Hsq
  apply mul_nonneg (le_trans zero_le_one (le_max_left _ _))
  rw [show 20 * (r + 1) = 2 * (10 * (r + 1)) by ring, pow_mul]
  positivity

theorem arith (a a' d e A A' : ℝ) (n : ℕ) (ha : 0 ≤ a) (ha' : 0 ≤ a') (hd : 0 < d) (he : 0 < e) (hA : 0 ≤ A)
    (hA' : 0 ≤ A') (h : a ^ 2 * d / e ≤ A ^ n) (h' : a' ^ 2 * d / e ≤ A' ^ n) :
    a' * a * d / e ≤ Real.sqrt (A * A') ^ n := by
  have h2 : (Real.sqrt (A * A') ^ n) ^ 2 = A ^ n * A' ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (mul_nonneg hA hA'), mul_pow]
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1
  rw [h2]
  calc (a' * a * d / e) ^ 2 = (a ^ 2 * d / e) * (a' ^ 2 * d / e) := by ring
    _ ≤ A ^ n * A' ^ n := mul_le_mul h h' (by positivity) (by positivity)

end GlobalTheory.SupTau
