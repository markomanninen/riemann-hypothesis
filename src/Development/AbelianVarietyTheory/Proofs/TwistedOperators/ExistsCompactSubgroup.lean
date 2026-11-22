module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviEmbMulSingle

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.UnipCompact

variable {n : Type}

theorem conc_mul_sub (c : n → ℤ) (m : ℕ) : GlobalTheory.IwahoriInj.Conc fun i j => (m : ℤ) * (c i - c j) :=
  ⟨fun i => by simp, fun i j l => le_of_eq (by ring)⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Fintype n] [DecidableEq n]

theorem isClosed_unipOf (c : n → ℤ) : IsClosed (GlobalTheory.InertSupp.unipOf k c : Set (GL n k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have e : (GlobalTheory.InertSupp.unipOf k c : Set (GL n k)) =
      ⋂ i, ⋂ j, ⋂ (_ : ¬ c i < c j), {g : GL n k | (g : Matrix n n k) i j = (1 : Matrix n n k) i j} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipOf, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

theorem eventually_mem_grp {c : n → ℤ} {u : GL n k} (hu : u ∈ GlobalTheory.InertSupp.unipOf k c) :
    ∀ᶠ m : ℕ in Filter.atTop, u ∈ GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) := by
  have key : ∀ u ∈ GlobalTheory.InertSupp.unipOf k c, ∀ᶠ m : ℕ in Filter.atTop,
      ∀ i j, Deep ((m : ℤ) * (c i - c j)) (u.val i j) := by
    intro u hu
    simp only [Filter.eventually_all]
    intro i j
    by_cases h : c i < c j
    · filter_upwards [GlobalTheory.IwahoriInj.eventually_deep (u.val i j)] with m hm
      refine hm.mono ?_
      nlinarith [Int.natCast_nonneg m]
    · rw [GlobalTheory.InertSupp.mem_unipOf.1 hu i j h]
      refine Filter.Eventually.of_forall fun m => ?_
      by_cases hij : i = j
      · subst hij
        simp [GlobalTheory.IwahoriInj.deep_zero_iff]
      · simp [one_apply_ne hij, GlobalTheory.IwahoriInj.deep_zero]
  exact (key u hu).and (key _ (inv_mem hu))

theorem exists_compact_subgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : n → ℤ) (S : Finset (GL n k))
    (hS : ∀ u ∈ S, u ∈ GlobalTheory.InertSupp.unipOf k c) :
    ∃ H : Subgroup (GL n k), H ≤ GlobalTheory.InertSupp.unipOf k c ∧ IsCompact (H : Set (GL n k)) ∧ ∀ u ∈ S, u ∈ H := by
  obtain ⟨m, hm⟩ := ((Filter.eventually_all_finset S).2 fun u hu => eventually_mem_grp (hS u hu)).exists
  refine ⟨GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) ⊓ GlobalTheory.InertSupp.unipOf k c, inf_le_right, ?_,
    fun u hu => ⟨hm u hu, hS u hu⟩⟩
  rw [Subgroup.coe_inf]
  let f : n → n → ℤ := fun i j => (m : ℤ) * (c i - c j)
  have hK : IsCompact {A : Matrix n n k | ∀ i j, Deep (f i j) (A i j)} := by
    have h : IsCompact (Set.pi Set.univ fun i : n => Set.pi Set.univ fun j : n =>
        {x : k | Deep (f i j) x}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
        IsNonarchimedeanLocalField.isCompact_closedBall k _
    have e : {A : Matrix n n k | ∀ i j, Deep (f i j) (A i j)} =
        (Set.pi Set.univ fun i : n => Set.pi Set.univ fun j : n =>
          {x : k | Deep (f i j) x}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]
    exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  have hgrp : IsCompact (GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) : Set (GL n k)) := by
    convert h using 1
    ext g
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply,
      Set.mem_prod, (MulOpposite.op_injective).mem_set_image]
    rfl
  exact hgrp.inter_right (isClosed_unipOf c)

end GlobalTheory.UnipCompact
