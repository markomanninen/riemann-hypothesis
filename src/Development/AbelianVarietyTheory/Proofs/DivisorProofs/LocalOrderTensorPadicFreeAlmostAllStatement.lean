module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicFreeAlmostAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsScalarTowerCenAlgebra

@[expose] public section

open scoped TensorProduct
open GlobalTheory.LKInvGood
open GlobalTheory.LocMatrix in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localOrderTensorPadic_free_almost_all : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [FiniteDimensional F B] (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ),
    Module.Finite ℤ Λ → (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ;
      Module.Free (cenOrder ℓ F) (locOrder ℓ Λ) ∧
        Module.finrank (cenOrder ℓ F) (locOrder ℓ Λ) = Module.finrank F B := by
  intro F B _ _ _ _ _ _ _ Λ hΛ hfin hspan
  obtain ⟨v, hvΛ⟩ := exists_basis_mem (F := F) Λ hspan
  obtain ⟨D, hD, hDΛ⟩ := exists_den Λ hfin v
  refine ⟨D, hD, fun ℓ _ hℓ => ?_⟩
  let inst := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
  have hBasis : Nonempty (Module.Basis (Fin (Module.finrank F B)) (cenOrder ℓ F) (locOrder ℓ Λ)) := by
    let w : Fin (Module.finrank F B) → locOrder ℓ Λ := fun i =>
      ⟨(1 : ℚ_[ℓ]) ⊗ₜ v i, Algebra.subset_adjoin ⟨_, hvΛ i, rfl⟩⟩
    have hsum (c : Fin (Module.finrank F B) → cenOrder ℓ F) :
        ((∑ i, c i • w i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) =
          combMap (F := F) ℓ v (fun i => (c i : ℚ_[ℓ] ⊗[ℚ] F)) := by
      rw [AddSubmonoidClass.coe_finsetSum, combMap_apply]
      rfl
    have hli : LinearIndependent (cenOrder ℓ F) w := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have h0 : combMap (F := F) ℓ v (fun i => (c i : ℚ_[ℓ] ⊗[ℚ] F)) = combMap (F := F) ℓ v 0 := by
        rw [← hsum, hc, map_zero]
        rfl
      exact Subtype.ext (congrFun (combMap_injective ℓ v h0) i)
    have hsp : ⊤ ≤ Submodule.span (cenOrder ℓ F) (Set.range w) := by
      rintro ⟨z, hz⟩ -
      obtain ⟨c, hc⟩ := exists_coeffs ℓ Λ v D hDΛ hℓ z hz
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext ((hsum c).trans hc.symm)⟩
    exact ⟨Module.Basis.mk hli hsp⟩
  have : Nontrivial (ℚ_[ℓ] ⊗[ℚ] F) := by
    apply Module.nontrivial_of_finrank_pos (R := ℚ_[ℓ])
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos
  obtain ⟨basis⟩ := hBasis
  exact ⟨Module.Free.of_basis basis, by rw [Module.finrank_eq_card_basis basis, Fintype.card_fin]⟩
