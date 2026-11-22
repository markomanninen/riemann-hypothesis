module

public import Mathlib
public import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
public import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes

@[expose] public section

noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def ZeroCount : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ t : ℝ,
    zsumR χ t 1 (fun _ => 1) ≤ C * Real.log (q * (|t| + 2))

end GlobalTheory.Mem.An
