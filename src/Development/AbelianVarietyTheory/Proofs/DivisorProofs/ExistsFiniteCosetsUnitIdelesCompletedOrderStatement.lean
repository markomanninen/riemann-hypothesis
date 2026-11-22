module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCosetsUnitIdelesCompletedOrder
public import Formalism.PairingDivisors.StatementA
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_cosets_unitIdeles_completedOrder : ∀ (E : Type) [Field E] [NumberField E] (c : Ideal (OF E)), c ≠ ⊥ → ∃ R : Finset (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) = 1) → ∃ r ∈ R, r⁻¹ * y ∈ hatOUnits c := by
  first | exact @GlobalTheory.CMVal.Euler.exists_finset_cover_units | exact GlobalTheory.CMVal.Euler.exists_finset_cover_units | (intros; apply GlobalTheory.CMVal.Euler.exists_finset_cover_units <;> assumption)
