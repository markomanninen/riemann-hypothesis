module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceClosedUnderConjReflection
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

@[expose] public section

open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartzSpace_closed_under_conj_reflection : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by
  first | exact @GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection | exact GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection | (intros; apply GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection <;> assumption)
