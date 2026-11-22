module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylRepInvMulDiag

@[expose] public section

noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory

namespace WeylCell

namespace WeylUnipotentShell

theorem swap_lt_swap_iff_of_add_two {n : ℕ} (A A' a b : Fin n) (hA : A'.val = A.val + 2) (hab : a < b) :
    Equiv.swap A A' a < Equiv.swap A A' b ↔ (a < A ∨ A' < b) := by
  rw [Fin.lt_iff_val_lt_val] at hab
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 h3 h4 <;>
    simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff] at * <;> omega

theorem val_rev_lo_of_last {n : ℕ} (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (hn : ¬ Even n) :
    ((lo k).rev : Fin n).val = (lo k).val + 2 := by
  have h2 := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hn)
  have := k.isLt
  simp only [Fin.val_rev, lo, Fin.coe_castLE]
  omega

theorem mem_cellU_last_iff : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ u : GU σ n, u ∈ cellU y ↔ IsUnipU u ∧ ∀ i j : Fin n, i < j → (i < lo k ∨ (lo k).rev < j) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  intro L _ _ _ ϖ σ q _ n k hk hn y _ hy u
  have hw : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp [simpleU, hk]
  have hA := val_rev_lo_of_last k hk hn
  rw [hw] at hy
  let M : GL (Fin n) L → Matrix (Fin n) (Fin n) L := fun x => x.val
  have weylRep_inv_mul_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (p : Fin n) :
      (M x⁻¹) p (w p) * (M x) (w p) p = 1 := by
    have h : (M (x⁻¹ * x)) p p = (M (1 : GL (Fin n) L)) p p := by rw [inv_mul_cancel]
    dsimp only [M] at h
    rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
    rwa [Finset.sum_eq_single (w p) (fun b _ hb => by rw [hx b p hb, mul_zero]) (by simp)] at h

  have weylRep_mul_inv_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (p : Fin n) :
      (M x) (w p) p * (M x⁻¹) p (w p) = 1 := by
    have h : (M (x * x⁻¹)) (w p) (w p) = (M (1 : GL (Fin n) L)) (w p) (w p) := by rw [mul_inv_cancel]
    dsimp only [M] at h
    rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
    rwa [Finset.sum_eq_single p (fun b _ hb => by
        rw [hx (w p) b (fun e => hb (w.injective e).symm), zero_mul]) (by simp)] at h

  have weylRep_inv {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) : IsWeylRep w⁻¹ x⁻¹ := by
    intro p a hpa
    have hne : (M x) a (w⁻¹ a) ≠ 0 := by
      intro h0
      have := weylRep_mul_inv_diag hx (w⁻¹ a)
      rw [show w (w⁻¹ a) = a by simp] at this
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    have h : (M (x⁻¹ * x)) p (w⁻¹ a) = (M (1 : GL (Fin n) L)) p (w⁻¹ a) := by rw [inv_mul_cancel]
    dsimp only [M] at h
    rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_ne hpa] at h
    rw [Finset.sum_eq_single a (fun b _ hb => by
        rw [hx b (w⁻¹ a) (by simpa using hb), mul_zero]) (by simp)] at h
    exact (mul_eq_zero.1 h).resolve_right hne

  have weylRep_conj_apply {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (u : GL (Fin n) L)
      (p q : Fin n) : (M (x⁻¹ * u * x)) p q = (M x⁻¹) p (w p) * (M u) (w p) (w q) * (M x) (w q) q := by
    have hi := weylRep_inv hx
    dsimp only [M]
    rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (w q)
      (fun b _ hb => by rw [hx b q hb, mul_zero]) (by simp), Matrix.mul_apply,
      Finset.sum_eq_single (w p) (fun b _ hb => by rw [hi p b (fun e => hb (by rw [e]; simp)), zero_mul]) (by simp)]

  dsimp only [M] at weylRep_inv_mul_diag weylRep_mul_inv_diag weylRep_conj_apply
  have mem_cell_iff {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (u : GL (Fin n) L) :
      u ∈ cell x ↔ u ∈ unipB L (Fin n) ∧ ∀ a b, a < b → w⁻¹ a < w⁻¹ b → (M u) a b = 0 := by
    dsimp only [M]
    rw [mem_cell, mem_unipBLower]
    refine and_congr_right fun hu => ?_
    rw [mem_unipB] at hu
    constructor
    · rintro ⟨hl, -⟩ a b hab hw
      have h := hl _ _ hw
      rw [weylRep_conj_apply hx, show w (w⁻¹ a) = a by simp, show w (w⁻¹ b) = b by simp] at h
      have h1 := weylRep_inv_mul_diag hx (w⁻¹ a)
      have h2 := weylRep_mul_inv_diag hx (w⁻¹ b)
      rw [show w (w⁻¹ a) = a by simp] at h1
      rw [show w (w⁻¹ b) = b by simp] at h2
      rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · rw [h, zero_mul] at h1; exact absurd h1 zero_ne_one
        · exact h
      · rw [h, zero_mul] at h2; exact absurd h2 zero_ne_one
    · intro h
      refine ⟨fun p q hpq => ?_, fun p => ?_⟩
      · rw [weylRep_conj_apply hx]
        rcases lt_or_gt_of_ne (fun e : w p = w q => hpq.ne (w.injective e)) with hl | hl
        · rw [h _ _ hl (by simpa using hpq), mul_zero, zero_mul]
        · rw [hu.1 _ _ hl, mul_zero, zero_mul]
      · rw [weylRep_conj_apply hx, hu.2, mul_one, weylRep_inv_mul_diag hx]

  rw [cellU, Subgroup.mem_subgroupOf, mem_cell_iff hy, mem_unipB, Equiv.swap_inv]
  unfold IsUnipU IsBorelU
  refine and_congr_right fun _ => forall₂_congr fun a b => ?_
  constructor
  · intro h hab hor
    exact h hab ((swap_lt_swap_iff_of_add_two _ _ a b hA hab).2 hor)
  · intro h hab hs
    exact h hab ((swap_lt_swap_iff_of_add_two _ _ a b hA hab).1 hs)

end WeylUnipotentShell

end WeylCell

end GlobalTheory
