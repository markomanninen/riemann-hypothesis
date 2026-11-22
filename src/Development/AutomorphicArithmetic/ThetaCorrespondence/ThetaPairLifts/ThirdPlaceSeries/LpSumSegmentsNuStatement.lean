module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSegmentsLanglandsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LpSumSegmentsNu
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_segments_langlands_at_place : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    ∀ (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (l : List (Segment (w.adicCompletion E))) (c : ℝ),
      sumList ((l.map fun Γ => Γ.nu (c : ℂ)).map fun Δ =>
          ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)) =
        (sumList (l.map fun Δ => ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len))).lpTw c := by
  intro E Ω _ _ _ _ _ A w
  let _ := GlobalTheory.LocalData.complRel w
  have _ := GlobalTheory.LocalData.isLocalField w
  intro h rc hrc l c
  obtain ⟨a, ha, L⟩ := hrc
  rw [← GlobalTheory.NuShift.sumList_lpTw, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun Γ _ => ?_
  show ((rc (Γ.first.nu (c : ℂ))).lpTw _).lpChar _ = _
  have hnu := L.nu Γ.first c
  rw [hnu, WD.lpTw_add, add_comm, ← WD.lpTw_add, GlobalTheory.NuShift.lpChar_lpTw]
  rfl
end
