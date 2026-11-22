module

public import Mathlib
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalRingCardinality.DataTheta

@[expose] public section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff ENNReal
open Formalism.MainNotions.S

noncomputable section

namespace Formalism.MainNotions.CayleySignature

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def lam48 (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Fin (2 * r + k + 1) → ℝ :=
  fun i => if h : i.val < k - 1 then v ⟨i.val, h⟩
    else -b ⟨i.val - (k - 1), by have := i.isLt; omega⟩

def eps48 (k r : ℕ) : Fin (2 * r + k + 1) → Bool :=
  fun i => if i.val < k - 1 then true else decide ((i.val - (k - 1)) % 2 = 0)

def InterlacingCondition (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  (∀ i : Fin (k - 1), v i < u ⟨i.val, by have := i.isLt; omega⟩ ∧
      u ⟨i.val + 1, by have := i.isLt; omega⟩ < v i) ∧
    ∀ h : 0 < k, -b ⟨0, by omega⟩ < u ⟨k - 1, by omega⟩

def HalfIntegralDifference (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ i s, ∃ j : ℤ, u i - lam48 k r v b s = (j : ℝ) + 1 / 2

def rk48 (k r : ℕ) : ℕ := 2 * r + k + 1

def GapBig (k r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∃ t : ℕ, Odd t ∧ rk48 k r + 5 ≤ t ∧ 1801 ≤ rk48 k r + t ∧
    ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      2 * ((rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 < b ⟨j.val + 1, hj⟩ - b j

def GapC (C : ℝ) (k r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
    C * (rk48 k r : ℝ) ^ 3 < b ⟨j.val + 1, hj⟩ - b j

def LowGapGe (h : ℝ) (r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2), h ≤ b ⟨j.val + 1, hj⟩ - b j

def RealPlaceNumericalSetting (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ)
    (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  1 ≤ k ∧ Even k ∧ Formalism.QuantumDeterminants.inWb k r z ∧ 0 < Formalism.QuantumDeterminants.Tz k r z ∧ (∀ a, c a ≠ 0) ∧
    Formalism.QuantumDeterminants.IsHCParam u ∧ Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) ∧ InterlacingCondition k r u v b ∧
    HalfIntegralDifference k r u v b ∧ GapBig k r b

end Formalism.MainNotions.CayleySignature
