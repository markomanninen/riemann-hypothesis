module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Formalism.LocalToGlobal.CharacterGerms.RowTieTop
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound

@[expose] public section

open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.AddChar


open MvPowerSeries in
theorem subst_zero_eq {C : Type} [Field C] {κ τ : Type} [Fintype κ] (F : MvPowerSeries κ C) :
    MvPowerSeries.subst (fun _ : κ => (0 : MvPowerSeries τ C)) F = MvPowerSeries.C (constantCoeff F) := by
  classical
  have hs : HasSubst (fun _ : κ => (0 : MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  ext m
  rw [coeff_subst hs, finsum_eq_single _ 0]
  · simp [coeff_one, coeff_C]
  · intro d hd
    obtain ⟨w, hw⟩ := Finsupp.ne_iff.1 hd
    have : (d.prod fun s e => (0 : MvPowerSeries τ C) ^ e) = 0 := by
      refine Finset.prod_eq_zero (i := w) (by simpa using hw) ?_
      exact zero_pow (by simpa using hw)
    simp [this]


open MvPowerSeries in
theorem eq_mvExp_of_additive : ∀ (C : Type) [Field C] [CharZero C] (κ : Type) [Fintype κ] (U : MvPowerSeries κ C), MvPowerSeries.constantCoeff U = 1 → MvPowerSeries.subst (fun i : κ => (MvPowerSeries.X ((0 : Fin 2), i) + MvPowerSeries.X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) U = MvPowerSeries.subst (fun i : κ => (MvPowerSeries.X ((0 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) U * MvPowerSeries.subst (fun i : κ => (MvPowerSeries.X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) U → U = mvExp (∑ i : κ, MvPowerSeries.coeff (Finsupp.single i 1) U • (MvPowerSeries.X i : MvPowerSeries κ C)) := by
  classical
  intro C _ _ κ _ U h0 h
  have hA : HasSubst (fun i : κ => (X ((0 : Fin 2), i) + X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  have hB : ∀ a : Fin 2, HasSubst (fun i : κ => (X (a, i) : MvPowerSeries (Fin 2 × κ) C)) := fun a =>
    hasSubst_of_constantCoeff_zero (by simp)
  let p : Fin 2 × κ → MvPowerSeries κ C := fun x => if x.1 = 0 then X x.2 else 0
  have hp : HasSubst p := hasSubst_of_constantCoeff_zero (by
    intro x; simp only [p]; split_ifs <;> simp)
  have hE : constantCoeff U = 1 ∧ ∀ w, pderiv w U = coeff (Finsupp.single w 1) U • U := by
    refine ⟨h0, fun w => ?_⟩
    have h1 := congrArg (pderiv (R := C) ((1 : Fin 2), w)) h
    rw [Derivation.leibniz, Formalism.G.LogCR.pderiv_subst (by simp), Formalism.G.LogCR.pderiv_subst (by simp),
      Formalism.G.LogCR.pderiv_subst (by simp), Finset.sum_eq_single w, Finset.sum_eq_single w,
      Finset.sum_eq_zero] at h1
    · simp [pderiv_X, Pi.single_apply] at h1
      have h2 := congrArg (subst p) h1
      rw [subst_mul hp, subst_comp_subst_apply hA hp, subst_comp_subst_apply (hB 0) hp,
        subst_comp_subst_apply (hB 1) hp] at h2
      simp only [subst_add hp, subst_X hp, p] at h2
      simp [subst_zero_eq] at h2
      have hs : ∀ F : MvPowerSeries κ C, subst (fun s : κ => (X s : MvPowerSeries κ C)) F = F :=
        fun F => congrFun subst_self F
      rw [hs, hs] at h2
      rw [h2, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, smul_eq_C_mul, mul_comm]
      simp
    all_goals simp +contextual [pderiv_X, Pi.single_apply]
  have hcoeff : ∀ (F : MvPowerSeries κ C),
      (constantCoeff F = 1 ∧ ∀ w, pderiv w F = coeff (Finsupp.single w 1) U • F) →
      ∀ (n : ℕ) (m : κ →₀ ℕ), m.degree = n →
      (mfact m : C) * coeff m F = m.prod (fun s k => coeff (Finsupp.single s 1) U ^ k) := by
    intro F h
    intro n
    induction n with
    | zero =>
      intro m hm
      rw [Finsupp.degree_eq_zero_iff] at hm
      subst hm
      simp [mfact, h.1]
    | succ n ih =>
      intro m hm
      have hne : m ≠ 0 := by rintro rfl; simp at hm
      obtain ⟨w, hw⟩ := Finsupp.ne_iff.1 hne
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single w 1 := by
        refine ⟨m - Finsupp.single w 1, ?_⟩
        rw [tsub_add_cancel_of_le]
        rw [Finsupp.single_le_iff]
        simp at hw; omega
      have hd : m'.degree = n := by
        rw [map_add (f := _), Finsupp.degree_single] at hm; omega
      have h1 := congrArg (MvPowerSeries.coeff m') (h.2 w)
      rw [coeff_pderiv, coeff_smul] at h1
      have h2 : mfact (m' + Finsupp.single w 1) = (m' w + 1) * mfact m' := by
        unfold mfact
        have e1 := Finsupp.mul_prod_erase' (m' + Finsupp.single w 1) w (fun _ k => k.factorial) (by simp)
        have e2 := Finsupp.mul_prod_erase' m' w (fun _ k => k.factorial) (by simp)
        rw [← e1, ← e2, Finsupp.erase_add, Finsupp.erase_single, add_zero]
        simp [Nat.factorial_succ, mul_assoc]
      rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), ← ih m' hd, h2,
        Finsupp.prod_single_index (by simp)]
      push_cast
      linear_combination (mfact m' : C) * h1
  have hF : constantCoeff (mvExp (∑ i : κ, coeff (Finsupp.single i 1) U • (X i : MvPowerSeries κ C))) = 1 ∧
      ∀ w, pderiv w (mvExp (∑ i : κ, coeff (Finsupp.single i 1) U • (X i : MvPowerSeries κ C))) =
        coeff (Finsupp.single w 1) U • mvExp (∑ i : κ, coeff (Finsupp.single i 1) U • (X i : MvPowerSeries κ C)) := by
    constructor
    · rw [← coeff_zero_eq_constantCoeff_apply, (show ∀ (h : MvPowerSeries κ C) (m : κ →₀ ℕ), coeff m (mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) from fun _ _ => rfl)]; simp
    · intro w
      ext m
      have hL : pderiv w (∑ x, (coeff (Finsupp.single x 1) U) • (X x : MvPowerSeries κ C)) = MvPowerSeries.C ((coeff (Finsupp.single w 1) U)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_eq_single w]
        · simp [smul_eq_C_mul]
        · intro b _ hb; simp [pderiv_X_of_ne hb]
        · simp
      rw [coeff_pderiv, coeff_smul, (show ∀ (h : MvPowerSeries κ C) (m : κ →₀ ℕ), coeff m (mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) from fun _ _ => rfl), (show ∀ (h : MvPowerSeries κ C) (m : κ →₀ ℕ), coeff m (mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) from fun _ _ => rfl), map_add (f := _), Finsupp.degree_single,
        Finset.sum_range_succ', Finset.mul_sum, add_mul, Finset.sum_mul]
      have h0 : MvPowerSeries.coeff (m + Finsupp.single w 1)
          ((∑ x, (coeff (Finsupp.single x 1) U) • (X x : MvPowerSeries κ C)) ^ 0) = 0 := by
        rw [pow_zero, coeff_one, if_neg]
        intro h
        have := DFunLike.congr_fun h w
        simp at this
      rw [h0, zero_div, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 := coeff_pderiv (i := w) ((∑ x, (coeff (Finsupp.single x 1) U) • (X x : MvPowerSeries κ C)) ^ (k + 1)) m
      rw [pderiv_pow, hL, Nat.add_sub_cancel, ← map_natCast (MvPowerSeries.C (σ := κ) (R := C)),
        coeff_mul_C, coeff_C_mul] at h1
      have hk : (k.factorial : C) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
      have hk1 : ((k + 1 : ℕ) : C) ≠ 0 := by exact_mod_cast k.succ_ne_zero
      rw [div_mul_eq_mul_div, ← h1, Nat.factorial_succ]
      push_cast at hk1 ⊢
      field_simp
  ext m
  have hm : (mfact m : C) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    unfold mfact
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  exact mul_left_cancel₀ hm ((hcoeff U hE _ m rfl).trans (hcoeff _ hF _ m rfl).symm)

end GlobalTheory.AddChar
