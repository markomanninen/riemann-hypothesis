module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CapelliPolynomialPermutationMatch

@[expose] public section

open Finset Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_polynomial_permutation_match : ∀ (n M : ℕ) (lev : Fin n → ℕ) (χ : Fin n → ℂ) (P : Fin M → ℂ[X]) (s : Fin M → ℂ),
    (∀ a, lev a < M) → (∀ i, (P i).Monic ∧ (P i).natDegree = (univ.filter fun a => lev a = (i : ℕ)).card) →
    (∀ Y : ℂ, ∏ i, (P i).eval (Y + s i) = Formalism.QuantumDeterminants.capP χ Y) →
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin M,
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), χ (σ a) =
        (P i).nextCoeff + ((univ.filter fun a => lev a = (i : ℕ)).card : ℂ) * s i := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.exists_perm_of_monic_factors | exact GlobalTheory.CompanionTheory.RgCOBlock.exists_perm_of_monic_factors | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.exists_perm_of_monic_factors <;> assumption)
