module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericLevelOfFrameBlockAndCharacter
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum

@[expose] public section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericLevelOfFrame_block_and_character :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (ϖ : kˣ) (κ l : ℕ)
      (P : _root_.GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l)),
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsGenericLevel ψ ϖ P →
        ((∀ u ∈ N k (Fin κ) l 1, ∀ γ : GL (Fin κ) k, u * embX l γ ∈ P.J →
            ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧
          (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb →
            IsUpperUnip Fin.val gb.val → ∃ hm : embX l γ ∈ P.J,
              (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧
          ∀ u ∈ N k (Fin κ) l 1, ∀ hm : u ∈ P.J,
            (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u)) := by
  intro k _ _ _ _ ψ ϖ κ l P h
  have map_residue_apply {a : Type} [Fintype a] [DecidableEq a] (M : GL a 𝒪[k]) (i j : a) :
      ((GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) M : GL a 𝓀[k]) : Matrix a a 𝓀[k]) i j =
        IsLocalRing.residue 𝒪[k] ((M : Matrix a a 𝒪[k]) i j) := by
    simp

  have reduces_of_corner {g : GL (Fin κ ⊕ Fin l) k} {γ : GL (Fin κ) k}
      {g₀ : GL (Fin κ ⊕ Fin l) 𝒪[k]} (hg : GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀ = g)
      (hγ : (g : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k).toBlocks₁₁ = γ)
      (hres : ∀ r s : Fin κ, s ≤ r → IsLocalRing.residue 𝒪[k]
        ((g₀ : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) 𝒪[k]) (Sum.inl r) (Sum.inl s)) =
          (1 : Matrix (Fin κ) (Fin κ) 𝓀[k]) r s) :
      ∃ gb, Reduces γ gb ∧
        IsUpperUnip Fin.val (gb : Matrix (Fin κ) (Fin κ) 𝓀[k]) := by
    subst hg
    set A : Matrix (Fin κ) (Fin κ) 𝒪[k] :=
      (g₀ : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) 𝒪[k]).toBlocks₁₁
    have hB : ∀ r s, s ≤ r → IsLocalRing.residue 𝒪[k] (A r s) = (1 : Matrix (Fin κ) (Fin κ) 𝓀[k]) r s :=
      hres
    have hdet : IsUnit A.det := by
      apply IsLocalRing.notMem_maximalIdeal.1
      intro hm
      rw [← IsLocalRing.residue_eq_zero_iff, RingHom.map_det, Matrix.det_of_isUpperTriangular] at hm
      · have hp : ∏ i, (IsLocalRing.residue 𝒪[k]).mapMatrix A i i = 1 :=
          Finset.prod_eq_one fun i _ => by simp [RingHom.mapMatrix_apply, hB i i le_rfl]
        rw [hp] at hm
        exact one_ne_zero hm
      · intro i j hij
        have hij' : j < i := hij
        simp [RingHom.mapMatrix_apply, hB i j hij'.le, Matrix.one_apply_ne (ne_of_lt hij').symm]
    let γ₀ : GL (Fin κ) 𝒪[k] := A.nonsingInvUnit hdet
    refine ⟨GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) γ₀, ⟨γ₀, ?_, rfl⟩, ?_⟩
    · ext i j
      rw [← hγ]
      rfl
    · intro r s hsr
      rw [map_residue_apply]
      exact hres r s hsr

  have toBlocks₁₁_mul_embX_of_mem_N {u : GL (Fin κ ⊕ Fin l) k} (hu : u ∈ N k (Fin κ) l 1)
      (γ : GL (Fin κ) k) :
      ((u * embX l γ : GL (Fin κ ⊕ Fin l) k) :
        Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k).toBlocks₁₁ = γ := by
    rw [Units.val_mul, _root_.GlobalTheory.StepData.mul_toBlocks₁₁, _root_.GlobalTheory.RootEx.Radical.toBlocks₁₁_of_mem hu,
      _root_.GlobalTheory.RootEx.Radical.embX_val]
    simp

  have one_apply_inl_inl (r s : Fin κ) :
      (1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) 𝓀[k]) (Sum.inl r) (Sum.inl s) =
        (1 : Matrix (Fin κ) (Fin κ) 𝓀[k]) r s := by
    by_cases h : r = s <;> simp [Matrix.one_apply, h]

  have reduces_embX_of_reduces {γ : GL (Fin κ) k}
      {gb : GL (Fin κ) 𝓀[k]} (h : Reduces γ gb) :
      Reduces (embX l γ)
        (embX l gb) := by
    obtain ⟨γ₀, h₁, h₂⟩ := h
    subst h₁ h₂
    let g₀ : GL (Fin κ ⊕ Fin l) 𝒪[k] :=
      ⟨fromBlocks (γ₀ : Matrix (Fin κ) (Fin κ) 𝒪[k]) 0 0 1,
        fromBlocks ((γ₀⁻¹ : GL (Fin κ) 𝒪[k]) : Matrix (Fin κ) (Fin κ) 𝒪[k]) 0 0 1,
        by rw [fromBlocks_multiply]; simp, by rw [fromBlocks_multiply]; simp⟩
    refine ⟨g₀, ?_, ?_⟩ <;> ext i j <;> rcases i with i | i <;> rcases j with j | j <;>
      simp [g₀, _root_.GlobalTheory.RootEx.Radical.embX_val, Matrix.one_apply, apply_ite]

  have one_apply_inr_inr (r s : Fin l) :
      (1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) 𝓀[k]) (Sum.inr r) (Sum.inr s) =
        (1 : Matrix (Fin l) (Fin l) 𝓀[k]) r s := by
    by_cases h : r = s <;> simp [Matrix.one_apply, h]

  have hl (i : Fin κ) : framePos κ l (Sum.inl i) = i := rfl
  have hr (i : Fin l) : framePos κ l (Sum.inr i) = κ + i := rfl

  have superSum_framePos_embX (γ : GL (Fin κ) k) :
      superSum (framePos κ l)
          ((embX l γ : GL (Fin κ ⊕ Fin l) k) :
            Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) =
        superSum Fin.val (γ : Matrix (Fin κ) (Fin κ) k) := by
    unfold superSum
    simp only [Fintype.sum_sum_type, _root_.GlobalTheory.RootEx.Radical.embX_val, hl, hr,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply,
      ite_self, Finset.sum_const_zero, add_zero, zero_add]
    have h : ∑ i : Fin l, ∑ j : Fin l,
        (if κ + (j : ℕ) = κ + i + 1 then (1 : Matrix (Fin l) (Fin l) k) i j else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with hij
      · exact Matrix.one_apply_ne fun h => by subst h; omega
      · rfl
    linear_combination h

  have superSum_framePos_eq_simpleSum_of_mem_N {u : GL (Fin κ ⊕ Fin l) k} (hu : u ∈ N k (Fin κ) l 1) :
      superSum (framePos κ l)
          (u : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) =
        simpleSum u := by
    rw [_root_.GlobalTheory.RootEx.Model.mem_N_iff] at hu
    unfold InN at hu
    unfold superSum simpleSum
    simp only [Fintype.sum_sum_type, hl, hr]
    have h₁ : ∑ i : Fin κ, ∑ j : Fin κ, (if (j : ℕ) = i + 1 then
        (u : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) (Sum.inl i) (Sum.inl j) else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with hij
      · rw [hu _ _ (by simp [lev])]
        exact Matrix.one_apply_ne fun h => by
          have := congrArg (fun x : Fin κ ⊕ Fin l => Sum.elim (fun a : Fin κ => (a : ℕ)) (fun _ => 0) x) h
          simp at this
          omega
      · rfl
    have h₂ : ∑ i : Fin κ, ∑ j : Fin l, (if κ + (j : ℕ) = i + 1 then
        (u : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) (Sum.inl i) (Sum.inr j) else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with hij
      · rw [hu _ _ (by simp [lev]; omega)]
        simp
      · rfl
    have h₃ : ∑ i : Fin l, ∑ j : Fin κ, (if (j : ℕ) = κ + i + 1 then
        (u : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) (Sum.inr i) (Sum.inl j) else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rw [ite_eq_right (by omega)]
    have h₄ : ∀ i j : Fin l, (κ + (j : ℕ) = κ + i + 1) ↔ ((j : ℕ) = i + 1) := fun i j => by omega
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [h₄]
    linear_combination h₁ + h₂ + h₃
  unfold IsGenericLevel at h
  obtain ⟨hJ, hlam⟩ := h
  refine ⟨fun u hu γ hm => ?_, fun γ gb hred hup => ?_, fun u hu hm => ?_⟩
  · obtain ⟨gb', ⟨g₀, hg₀, hres₀⟩, hup'⟩ := (hJ _).1 hm
    refine reduces_of_corner hg₀ (toBlocks₁₁_mul_embX_of_mem_N hu γ) fun r s hsr => ?_
    rw [← map_residue_apply, hres₀]
    exact (hup' (Sum.inl r) (Sum.inl s) (by simpa [framePos] using hsr)).trans
      (one_apply_inl_inl r s)
  · have hm : embX l γ ∈ P.J := by
      refine (hJ _).2 ⟨embX l gb, reduces_embX_of_reduces hred, ?_⟩
      intro r s hrs
      rcases r with r | r <;> rcases s with s | s
      · have h' : (s : ℕ) ≤ r := by simpa [framePos] using hrs
        rw [_root_.GlobalTheory.RootEx.Radical.embX_val, fromBlocks_apply₁₁]
        exact (hup r s h').trans (one_apply_inl_inl r s).symm
      · have h' : κ + (s : ℕ) ≤ r := by simpa [framePos] using hrs
        omega
      · rw [_root_.GlobalTheory.RootEx.Radical.embX_val, fromBlocks_apply₂₁]
        simp
      · rw [_root_.GlobalTheory.RootEx.Radical.embX_val, fromBlocks_apply₂₂]
        exact (one_apply_inr_inr r s).symm
    refine ⟨hm, ?_⟩
    rw [hlam ⟨_, hm⟩]
    simp only [superSum_framePos_embX]
  · rw [hlam ⟨u, hm⟩, superSum_framePos_eq_simpleSum_of_mem_N hu]
