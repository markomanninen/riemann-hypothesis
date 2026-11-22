module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZalgEqAdjoinFiniteCapelli
public import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonic

@[expose] public section

open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zalg_eq_adjoin_finite_capelli : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ), ∃ T : Finset (Module.End ℂ (Sm E b)), (∀ t ∈ T, ∃ (τ : E →+* ℂ) (u : ℂ), t = cap τ u) ∧ Zalg E b = Algebra.adjoin ℂ (T : Set (Module.End ℂ (Sm E b))) := by
  first | exact @GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps | exact GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps | (intros; apply GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps <;> assumption)
