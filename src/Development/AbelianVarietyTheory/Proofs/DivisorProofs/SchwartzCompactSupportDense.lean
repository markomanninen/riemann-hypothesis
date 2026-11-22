module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzDenseHasCompactSupport

@[expose] public section

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace GlobalTheory

theorem schwartz_mem_closure_hasCompactSupport :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : SchwartzMap V ℂ),
    f ∈ closure {g : SchwartzMap V ℂ | HasCompactSupport (g : V → ℂ)} := by
  intro V _ _ _ f
  exact schwartz_dense_hasCompactSupport f

end GlobalTheory
