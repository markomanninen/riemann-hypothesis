module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBiorthogonalFrameOfSaturatedFlag
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_biorthogonal_frame_of_saturated_flag : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ), Monotone F → F 0 = ⊥ → (∀ b, m ≤ b → F b = F m) → Submodule.IsFullLattice E (F m) → (∀ b, ∀ y ∈ F m, y ∈ Submodule.span E (F b : Set (Fin n → E)) → y ∈ F b) → (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) → ∃ (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' ∧ (∀ b, Submodule.IsFullLattice E (Λ b)) ∧ ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0) := by
  first
  | exact @GlobalTheory.RadCov.exists_biorth_of_saturated_flag
  | intro E _ _ n m F r hmono h0 hm hL hsat hrk
    obtain ⟨T, T', Λ, hB, hΛ, hmem⟩ :=
      GlobalTheory.RadCov.exists_biorth_of_saturated_flag E n m F r hmono h0 hm
        hL.toIsLattice hsat hrk
    refine ⟨T, T', Λ, hB, ?_, hmem⟩
    intro b
    let : Submodule.IsLattice E (Λ b) := hΛ b
    refine { span_eq_top := ?_ }
    apply eq_top_iff.mpr
    intro v _
    have hle : Submodule.span E (F m : Set (Fin n → E)) ≤
        (Submodule.span E (Λ b : Set (Fin (r b) → E))).comap (T' b).mulVecLin := by
      apply Submodule.span_le.mpr
      intro x hx
      exact Submodule.subset_span ((hmem m x).1 hx b).1
    have hx : T' b *ᵥ (T b *ᵥ v) ∈ Submodule.span E (Λ b : Set (Fin (r b) → E)) :=
      hle (by rw [hL.span_eq_top]; trivial)
    rw [Matrix.mulVec_mulVec, hB.1 b, Matrix.one_mulVec] at hx
    exact hx
