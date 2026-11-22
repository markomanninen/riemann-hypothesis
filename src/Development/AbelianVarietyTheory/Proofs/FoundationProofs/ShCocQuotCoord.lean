module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
public import ReciprocityTheory.GaloisValuations.Global

@[expose] public section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.KA

theorem shCoc_quot_coord : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω)
    (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (ν : G ℚ Ω → (Qbar l)ˣ)
    (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (m : ℕ),
    GlobalTheory.KA.ShCoc ρ (cycMod (F := ℚ) (Ω := Ω) l m)⁻¹ (Y m) →
    (∀ s ∈ Dec (F := ℚ) A, ρ s 1 0 = 0 ∧ ρ s 1 1 = (ν s : Qbar l)) →
    ∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ∀ x,
      Y m (s * t) x 1 = Y m s x 1 + (ν s : Qbar l) * Y m t (x * (cycMod ℚ Ω l m s)⁻¹) 1 := by
  intro l _ Ω _ _ A ρ ν Y m hY hρ s hs t _ x
  simpa only [Pi.add_apply, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, (hρ s hs).1,
    (hρ s hs).2, zero_mul, zero_add, MonoidHom.inv_apply] using congrFun (hY s t x) 1

end GlobalTheory.KA
