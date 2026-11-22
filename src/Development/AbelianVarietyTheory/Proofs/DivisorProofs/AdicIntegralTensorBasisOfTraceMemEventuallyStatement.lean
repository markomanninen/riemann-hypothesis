module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisOfTraceMemEventually
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsIntegralConj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscrMulMemOfIsIntegral

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicIntegralTensorBasis_of_trace_mem_eventually : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (bL : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ E : v.adicCompletion ℚ ⊗[ℚ] L,
      (∀ i, Algebra.trace (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)
          (E * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] bL i)) ∈ v.adicCompletionIntegers ℚ) →
        IsIntB v bL E := by
  first | (exact @GlobalTheory.LocIntSpan.isIntB_of_trace_mem) | (exact GlobalTheory.LocIntSpan.isIntB_of_trace_mem) | (intros; apply GlobalTheory.LocIntSpan.isIntB_of_trace_mem  <;> assumption)
