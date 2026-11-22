module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntGeneratorsCardEqOfIsLatticePi

@[expose] public section

open scoped Matrix
open NumberField

theorem _root_.GlobalTheory.T.exists_int_span_generators_of_isLattice_pi
    (E : Type) [Field E] [NumberField E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Submodule.IsFullLattice E Λ) :
    ∃ u : Fin (Module.finrank ℚ E * n) → Fin n → E,
      (∀ x, x ∈ Λ ↔ x ∈ Submodule.span ℤ (Set.range u)) ∧
      Submodule.span ℚ (Set.range u) = ⊤ :=
  GlobalTheory.exists_intGenerators_card_eq_of_isLattice_pi E n Λ hΛ
