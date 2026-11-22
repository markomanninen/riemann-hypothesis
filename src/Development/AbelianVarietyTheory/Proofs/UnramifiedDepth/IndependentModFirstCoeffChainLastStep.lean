module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
public import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
public import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
public import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowAdditiveAndRoots

@[expose] public section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical GlobalTheory.FrobRoot

namespace GlobalTheory.LastStep

theorem mm_mul_int {C : Type} [Field C] {V : VF C} {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) :
    V.MM (a * b) := by
  unfold VF.MM VF.Ge at *
  rw [V.v.map_mul]
  exact add_pos_of_pos_of_nonneg ha (by simpa using hb)

theorem mm_sum {C : Type} [Field C] {V : VF C} {ι : Type} (s : Finset ι) (f : ι → C)
    (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by
  have mm_zero : V.MM (0 : C) := by
    unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos
  have mm_add : ∀ {a b : C}, V.MM a → V.MM b → V.MM (a + b) :=
    fun ha hb => V.v.map_lt_add ha hb
  induction s using Finset.induction_on with
  | empty => simpa using mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mm_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mm_of_tan {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
    {G : Cart V d I J} (S : Sys G) (w : I → C) (h : ∀ k, V.MM (∑ c, w c * S.tan c k)) (c : I) :
    V.MM (w c) := by
  have h1 : S.U * S.U⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr S.U_det_ne)
  have e : w c = ∑ k, (∑ b, w b * S.tan b k) * S.U⁻¹ k c := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ k, w b * S.tan b k * S.U⁻¹ k c = w b * (S.U * S.U⁻¹) b c := by
      intro b
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp only [Sys.U, Matrix.of_apply]; ring
    simp only [this, h1, Matrix.one_apply]
    simp
  rw [e]
  exact mm_sum _ _ fun k _ => mm_mul_int (h k) (inv_int S.U S.U_int S.unimod k c)

theorem indepMod_first_coeff : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → IndepMod V (fun δ (κ : J g) => ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), y δ c ^ V.l * ((V.l : C) * S.be c 1 κ)) := by
  intro C _ V d _ I J _ _ X hA g a ha i S Z D hD s hs m y hy hind co hco hsum
  have mm_add : ∀ {a b : C}, V.MM a → V.MM b → V.MM (a + b) :=
    fun ha hb => V.v.map_lt_add ha hb
  have mm_pow : ∀ {a : C}, V.MM a → ∀ {n : ℕ}, n ≠ 0 → V.MM (a ^ n) := by
    intro a ha n hn
    unfold VF.MM at *
    rw [V.v.map_pow]
    exact nsmul_pos ha hn
  have ge_of_pow : ∀ {a : C} {n : ℕ}, n ≠ 0 → V.Ge 0 (a ^ n) → V.Ge 0 a := by
    intro a n hn ha
    unfold VF.Ge at *
    rw [V.v.map_pow] at ha
    rw [WithTop.coe_zero] at ha ⊢
    by_contra h
    exact absurd ha (not_le.mpr (nsmul_neg (not_le.mp h) hn))
  let R : Subring C := {
    carrier := {x | V.Ge 0 x}
    mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
    one_mem' := VF.Ge.one
    add_mem' := fun ha hb => VF.Ge.add ha hb
    zero_mem' := VF.Ge.zero 0
    neg_mem' := fun ha => VF.Ge.neg ha }
  have mm_add_pow : ∀ (e : ℕ) {a b : C}, V.Ge 0 a → V.Ge 0 b →
      V.MM ((a + b) ^ (V.l ^ e) - (a ^ (V.l ^ e) + b ^ (V.l ^ e))) := by
    intro e a b ha hb
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq V.l_prime (⟨a, ha⟩ : R) (⟨b, hb⟩ : R) e
    have h := congrArg (Subtype.val) hr
    push_cast at h
    rw [h, add_sub_cancel_left]
    have hr0 : V.Ge 0 (r : C) := r.2
    have mm_of_ge_one : ∀ {x : C}, V.Ge 1 x → V.MM x := by
      intro x hx
      refine lt_of_lt_of_le ?_ hx
      exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
    apply mm_of_ge_one
    first
      | simpa using hr0.l_mul
      | simpa [mul_assoc] using (ha.mul_int (hb.mul_int hr0)).l_mul
  have mm_sum_pow : ∀ (e : ℕ) {ι : Type} (s : Finset ι) (x : ι → C),
      (∀ i ∈ s, V.Ge 0 (x i)) →
      V.MM ((∑ i ∈ s, x i) ^ (V.l ^ e) - ∑ i ∈ s, x i ^ (V.l ^ e)) := by
    intro e ι s x hx
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero e V.l_prime.ne_zero), sub_zero]
      unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hs : ∀ i ∈ s, V.Ge 0 (x i) := fun i hi => hx i (Finset.mem_insert_of_mem hi)
      have h := mm_add (mm_add_pow e (hx a (Finset.mem_insert_self a s)) (VF.Ge.sum hs)) (ih hs)
      convert h using 1 <;> ring
  haveI := X.algClosed
  have hl : V.l ≠ 0 := V.l_prime.ne_zero
  choose r hr using fun δ => IsAlgClosed.exists_pow_nat_eq (co δ) (Nat.pos_of_ne_zero hl)
  have hr0 : ∀ δ, V.Ge 0 (r δ) := fun δ => ge_of_pow hl (by rw [hr]; exact hco δ)
  set w : I g → C := fun c => ∑ δ, r δ * y δ c with hw
  have hw0 : ∀ c, V.Ge 0 (w c) := fun c => VF.Ge.sum fun δ _ => (hr0 δ).mul_int (hy δ c)
  set T := Finset.univ.filter (fun c => D.lev c = s) with hT
  have hbig : X.big g (a + ((2 * s : ℕ) : ZMod d)) :=
    (S4.parity_of_alt (X.big g) (CharacteristicFromRanks.alt_step X.big X.big_compl hA g) a ha (2 * s)).2 (even_two_mul s)
  have hgood : ∀ c ∈ T, (X.G g).Good (a + ((2 * s : ℕ) : ZMod d)) (S.tan c) (S.cur c) := by
    intro c hc
    have h1 : D.lev c = s := (Finset.mem_filter.1 hc).2
    have h2 : D.lev c < Formalism.BaseCaseIdentities.Kn i := h1 ▸ hs
    have h3 := hD.2.2.2.2 c h2
    rw [h1] at h3
    rw [← h3]
    exact hD.good (D.pure_good c (by rw [hD.2.2.1]; exact h2))
  have hG := Cart.Good.comb T (co := w) (fun c _ => hw0 c) hgood
  have hR := X.R2 hA g _ hbig _ _ hG (by
    intro κ
    rw [Cart.c0'_comb]
    have h1 : V.MM (∑ c ∈ T, (w c ^ V.l - ∑ δ, (r δ * y δ c) ^ V.l) * ((V.l : C) * S.be c 1 κ)) := by
      refine mm_sum _ _ fun c _ => mm_mul_int ?_ (l_mul_be_one_int S c κ)
      have := mm_sum_pow 1 Finset.univ (fun δ => r δ * y δ c) (fun δ _ => (hr0 δ).mul_int (hy δ c))
      simpa only [pow_one] using this
    have h2 := mm_add h1 (hsum κ)
    convert h2 using 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (t := T), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [mul_pow, hr, sub_mul, Finset.sum_mul, mul_assoc, sub_add_cancel]
    rfl)
  have hwm : ∀ c, V.MM (if D.lev c = s then w c else 0) := by
    refine mm_of_tan S _ fun k => ?_
    convert hR k using 1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hT, Finset.sum_filter, ite_mul, zero_mul]
  intro δ
  rw [← hr δ]
  refine mm_pow (hind r hr0 (fun c => ?_) δ) hl
  convert hwm c using 1
  by_cases hc : D.lev c = s <;> simp [hw, hc]

end GlobalTheory.LastStep
