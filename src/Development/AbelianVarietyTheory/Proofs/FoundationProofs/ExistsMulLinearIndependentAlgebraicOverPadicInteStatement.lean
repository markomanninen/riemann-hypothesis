module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulLinearIndependentAlgebraicOverPadicInte
public import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow

@[expose] public section

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_linearIndependent_algebraicOverPadicIntegers : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ y ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp (p := p) x},
    ∃ (n : ℕ) (a : Fin n → Ω) (f : Fin n → O0 p) (g : O0 p), (∀ i, IsAlgZp (p := p) (a i)) ∧
      LinearIndependent (O0 p) a ∧ g ≠ 0 ∧
      algebraMap (O0 p) Ω g * y = ∑ i, algebraMap (O0 p) Ω (f i) * a i := by
  exact @GlobalTheory.K5.algSpan_reprInd
