module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNonZeroDivisorsOfInvertibleSpanSingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_nonZeroDivisors_of_invertible_span_singleton' : ∀ (A : Type) [CommRing A] (d : A), Module.Invertible A ↥(Ideal.span {d}) → d ∈ nonZeroDivisors A := by
  first | exact @GlobalTheory.BSP.mem_nonZeroDivisors_of_invertible_span_singleton | exact GlobalTheory.BSP.mem_nonZeroDivisors_of_invertible_span_singleton | (intros; apply GlobalTheory.BSP.mem_nonZeroDivisors_of_invertible_span_singleton <;> assumption)
