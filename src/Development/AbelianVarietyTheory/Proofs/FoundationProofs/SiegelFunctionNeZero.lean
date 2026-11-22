module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem sg_ne_zero : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x → sg c x τ ≠ 0 :=
  fun _ _ τ h => (GlobalTheory.Sieg.Model.multipliable_and_sg_ne_zero h τ).2.2

end GlobalTheory.Sieg
