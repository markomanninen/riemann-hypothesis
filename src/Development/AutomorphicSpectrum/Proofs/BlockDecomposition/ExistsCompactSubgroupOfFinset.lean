module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactUnipotentInCompactSubgroup

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.UnipExhaust

theorem exists_compact_subgroup_of_finset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
      (s : Finset (GL (Fin N) k)), (↑s : Set (GL (Fin N) k)) ⊆ unipB k (Fin N) →
      ∃ L : Subgroup (GL (Fin N) k), L ≤ unipB k (Fin N) ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧
        IsCompact (L : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ N s hs
  let c : Fin N → ℤ := fun i => ((i : ℕ) : ℤ)
  have heq : unipB k (Fin N) = GlobalTheory.InertSupp.unipOf k c := by
    ext g
    rw [GlobalTheory.SmGL.mem_unipB, GlobalTheory.InertSupp.mem_unipOf]
    constructor
    · rintro ⟨h1, h2⟩ i j hij
      have hji : j ≤ i := by
        dsimp [c] at hij
        rw [not_lt] at hij
        exact Fin.le_def.2 (by exact_mod_cast hij)
      rcases hji.lt_or_eq with h | h
      · rw [h1 i j h, Matrix.one_apply_ne (ne_of_gt h)]
      · subst h; rw [h2 j, Matrix.one_apply_eq]
    · intro h
      refine ⟨fun i j hji => ?_, fun i => ?_⟩
      · have : ¬ ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by
          have := Fin.lt_def.1 hji
          omega
        rw [h i j this, Matrix.one_apply_ne (ne_of_gt hji)]
      · rw [h i i (lt_irrefl _), Matrix.one_apply_eq]
  have hQU : (↑s : Set (GL (Fin N) k)) ⊆ GlobalTheory.InertSupp.unipOf k c := by
    simpa [← heq] using hs
  let V : ℕ → Set (GL (Fin N) k) := fun m =>
    (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL (Fin N) k)) ∪ (GlobalTheory.InertSupp.unipOf k c : Set _)ᶜ
  have hVo : ∀ m, IsOpen (V m) := fun m =>
    (GlobalTheory.UnipCptSub.isOpen_grp c m).union (GlobalTheory.UnipCompact.isClosed_unipOf c).isOpen_compl
  have hVmono : Monotone V := by
    intro m M hmM g hg
    rcases hg with hg | hg
    · by_cases hu : g ∈ GlobalTheory.InertSupp.unipOf k c
      · left
        have key : ∀ x : GL (Fin N) k, x ∈ GlobalTheory.InertSupp.unipOf k c →
            (∀ i j, GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) (x.val i j)) →
            ∀ i j, GlobalTheory.IwahoriInj.Deep ((M : ℤ) * (c i - c j)) (x.val i j) := by
          intro x hx hd i j
          by_cases hij : c i < c j
          · refine (hd i j).mono ?_
            have : (m : ℤ) ≤ M := by exact_mod_cast hmM
            nlinarith
          · rw [GlobalTheory.InertSupp.mem_unipOf.1 hx i j hij]
            by_cases e : i = j
            · subst e
              simp [GlobalTheory.IwahoriInj.deep_zero_iff]
            · simp [Matrix.one_apply_ne e, GlobalTheory.IwahoriInj.deep_zero]
        exact ⟨key g hu hg.1, key g⁻¹ (inv_mem hu) hg.2⟩
      · exact Or.inr hu
    · exact Or.inr hg
  have hcov : (↑s : Set (GL (Fin N) k)) ⊆ ⋃ m, V m := fun g hg =>
    Set.mem_iUnion.2 (((GlobalTheory.UnipCompact.eventually_mem_grp (hQU hg)).exists).imp fun _ h => Or.inl h)
  obtain ⟨M, hM⟩ := s.finite_toSet.isCompact.elim_directed_cover V hVo hcov hVmono.directed_le
  refine ⟨GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c M) ⊓ unipB k (Fin N), inf_le_right, ?_, ?_⟩
  · intro g hg
    refine ⟨?_, hs hg⟩
    rcases hM hg with h | h
    · exact h
    · exact absurd (hQU hg) h
  · rw [Subgroup.coe_inf]
    apply (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right
    rw [heq]
    exact GlobalTheory.UnipCompact.isClosed_unipOf _

end GlobalTheory.CompanionTheory.UnipExhaust
