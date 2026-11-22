module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ActDiagMemOfWK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.CoordSpan

@[expose] public section

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

theorem fockCoordinates_span_finiteDimensional (n : ℕ) (ε : Fin n → Bool) (M : Type)
    [NormedAddCommGroup M] [InnerProductSpace ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (Z : Submodule ℂ (TensorProduct ℂ M (Fock n))) (hZ : FiniteDimensional ℂ Z)
    (hK : IsKStableSub ε (diagE ε (eT E) cpT cmT) Z) :
    FiniteDimensional ℂ (coordSpan Z) ∧ IsKStableSub ε E (coordSpan Z) := by
  have hle : coordSpan Z ≤ ⨆ s : Finset (Fin (n * n)), Z.map (tcoef (M := M) ((fockBasis n).coord s)) := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨s, y, hy, rfl⟩
    exact (le_iSup (fun s : Finset (Fin (n * n)) => Z.map (tcoef (M := M) ((fockBasis n).coord s))) s)
      (Submodule.mem_map_of_mem hy)
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  intro a b hab v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, y, hy, rfl⟩ := hx
    let X := Matrix.single a b (1 : ℂ)
    have e := tco_actDiag (ε := ε) E X y s
    simp only [X, TRGap.actM_single'] at e
    show E a b (tcoef ((fockBasis n).coord s) y) ∈ coordSpan Z
    rw [eq_sub_of_add_eq e.symm, tcoef_eq_sum ((fockBasis n).coord s ∘ₗ sgX ε X) y]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨s, _, hK a b hab y hy, rfl⟩) ?_
    refine Submodule.sum_mem _ fun s' _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s', y, hy, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.PsCo.PcEF
