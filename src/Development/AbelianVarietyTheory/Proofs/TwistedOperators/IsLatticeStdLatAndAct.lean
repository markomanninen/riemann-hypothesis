module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem isLattice_stdLat_and_act : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι], Submodule.IsLattice k (stdLat k ι) ∧ ∀ (g : GL ι k) (L : Submodule 𝒪[k] (ι → k)), Submodule.IsLattice k L → Submodule.IsLattice k (act g L) := by
  intro k _ _ _ _ ι _ _
  refine ⟨⟨?_, ?_⟩, fun g L hL => ⟨?_, ?_⟩⟩
  · unfold stdLat
    refine Submodule.fg_pi fun _ => ?_
    rw [Submodule.one_eq_span]
    exact Submodule.fg_span_singleton _
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · exact hL.fg.map _
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

end GlobalTheory.RootEx.UnfoldShape
