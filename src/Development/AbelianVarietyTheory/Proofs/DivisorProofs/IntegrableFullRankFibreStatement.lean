module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

@[expose] public section

open MeasureTheory Matrix Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_full_rank_fibre :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν : kˣ →* ℂˣ),
      GlobalTheory.SmGL.IsSmoothChar ν → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB (k := k) a (a + b),
      MeasureTheory.Integrable (fun g : GL (Fin a) k =>
        Φ (g.val * GlobalTheory.SplitFlip.X0 (k := k) finSumFinEquiv) *
          (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
          GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2))
        (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) := by
  intro k _ _ _ _ _ _ a b ν hν Φ hΦ
  obtain ⟨⟨hLocal, hCompact⟩, hRank⟩ := hΦ
  let σ := finSumFinEquiv (m := a) (n := b)
  let X₀ := GlobalTheory.SplitFlip.X0 (k := k) σ
  have hLocalΦ : IsLocallyConstant fun g : GL (Fin a) k => Φ (g.val * X₀) :=
    hLocal.comp_continuous (Units.continuous_val.matrix_mul continuous_const)
  have hLocalν := GlobalTheory.GodementJacquet.isLocallyConstant_char_det (k := k) (n := Fin a) hν
  have hLocalPow : IsLocallyConstant fun g : GL (Fin a) k =>
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) :=
    ((GlobalTheory.SplitWeil.isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det).comp
      fun x => ((x : ℝ) : ℂ) ^ (((a + b : ℕ) : ℂ) / 2)
  have hContinuous := ((hLocalΦ.mul hLocalν).mul hLocalPow).continuous

  let D : Set (Matrix (Fin a) (Fin a) k) := {A | Φ (A * X₀) ≠ 0}
  have hClosed : IsClosed D :=
    (hLocal.isOpen_fiber 0).isClosed_compl.preimage
      (show Continuous fun A : Matrix (Fin a) (Fin a) k => A * X₀ from
        continuous_id.matrix_mul continuous_const)
  have hSubset : D ⊆ (fun M : Matrix (Fin a) (Fin (a + b)) k => M * X₀ᵀ) '' tsupport Φ := by
    intro A hA
    refine ⟨A * X₀, subset_tsupport _ hA, ?_⟩
    have hTranspose : X₀ * X₀ᵀ = 1 := by
      ext i j
      change (GlobalTheory.SplitFlip.X0 (k := k) σ * X₀ᵀ) i j = _
      rw [GlobalTheory.SplitFlip.frameMatrixFirstColumnBlock_mul_apply]
      simp [X₀, GlobalTheory.SplitFlip.X0, Matrix.one_apply, eq_comm]
    show A * X₀ * X₀ᵀ = A
    rw [Matrix.mul_assoc, hTranspose, Matrix.mul_one]
  have hCompactD : IsCompact D :=
    (hCompact.image (show Continuous fun M : Matrix (Fin a) (Fin (a + b)) k => M * X₀ᵀ from
      continuous_id.matrix_mul continuous_const)).of_isClosed_subset hClosed hSubset
  have hRange : D ⊆ Set.range fun g : GL (Fin a) k => g.val := by
    intro A hA
    have hFullRank : (A * X₀).rank = a := by
      by_contra hne
      exact hA (hRank _ hne)
    have hRankA : A.rank = Fintype.card (Fin a) := by
      refine le_antisymm (by simpa using A.rank_le_width) ?_
      simpa [hFullRank] using Matrix.rank_mul_le_left A X₀
    have hIndependent : LinearIndependent k A.row := by
      rw [rank_eq_finrank_span_row] at hRankA
      rw [linearIndependent_iff_card_eq_finrank_span]
      exact hRankA.symm
    exact ⟨(Matrix.linearIndependent_row_iff_isUnit.1 hIndependent).unit, rfl⟩
  have hPreimage : IsCompact ((fun g : GL (Fin a) k => g.val) ⁻¹' D) :=
    GlobalTheory.SplitFlip.isEmbedding_val_GL.isInducing.isCompact_preimage' hCompactD hRange
  have hSupport : HasCompactSupport fun g : GL (Fin a) k =>
      Φ (g.val * X₀) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2) := by
    refine HasCompactSupport.intro hPreimage fun g hg => ?_
    have hZero : Φ (g.val * X₀) = 0 := not_not.1 hg
    simp [hZero]
  exact hContinuous.integrable_of_hasCompactSupport hSupport
