module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulMemSpanAlgebraicOverPadicIntegers
public import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow

@[expose] public section

open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_mem_span_algebraicOverPadicIntegers : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp (p := p) x}),
    ∃ g : O0 p, g ≠ 0 ∧ algebraMap (O0 p) Ω g * b ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp (p := p) x} := by
  first | exact @GlobalTheory.K5.ReprSpan.exists_mul_mem_span | exact GlobalTheory.K5.ReprSpan.exists_mul_mem_span | (intros; apply GlobalTheory.K5.ReprSpan.exists_mul_mem_span <;> assumption)
