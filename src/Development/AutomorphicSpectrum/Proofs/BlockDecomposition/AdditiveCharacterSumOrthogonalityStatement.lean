module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdditiveCharacterSumOrthogonality
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR

@[expose] public section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_character_sum_orthogonality : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (ψ₀ : AddChar K ℂ), ψ₀ ≠ 1 → ∀ x : Fin j → K,
    (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) = if x = 0 then (Fintype.card K : ℂ) ^ j else 0 := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.Orth.orth | exact GlobalTheory.CompanionTheory.TyFin.Orth.orth | (intros; apply GlobalTheory.CompanionTheory.TyFin.Orth.orth <;> assumption)
