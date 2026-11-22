module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTypeWeightMemConeOverLowestKType

@[expose] public section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (root)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsKTypeOf IsDS)
open CompanionTheory.D.LK (IsKMod)

theorem _root_.GlobalTheory.T.kType_weight_mem_cone_over_lowest_kType : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧ μ = lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  exact @GlobalTheory.kType_weight_in_cone_over_lowK
