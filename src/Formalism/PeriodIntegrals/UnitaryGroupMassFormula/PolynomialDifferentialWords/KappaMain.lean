module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaCoeff

@[expose] public section

open MvPolynomial Finsupp

noncomputable section

namespace PI.OpWords

theorem symbolMapInjective : KappaInj := by
  intro K _ _ k d A B h
  have hmono : ∀ g : Fin k →₀ ℕ, A (mono K k d g) = B (mono K k d g) := by
    intro g
    apply Subtype.ext
    ext m
    have h1 := congrArg (AddMonoidAlgebra.coeff · (Finsupp.sumElim m g)) h
    rw [coeff_kappa, coeff_kappa] at h1
    exact mul_left_cancel₀ (invFact_ne_zero g) h1
  apply LinearMap.ext
  intro F
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eq_sum_mono F, map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, map_smul, hmono g]

theorem symbolMapBihomogeneous : KappaBihom := by
  intro K _ _ k d A
  show kappa K k d A ∈ weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d
  have key : ∀ m g : Fin k →₀ ℕ, AddMonoidAlgebra.coeff (kappa K k d A) (Finsupp.sumElim m g) ≠ 0 →
      m.degree = d ∧ g.degree = d := by
    intro m g h
    rw [coeff_kappa] at h
    have h2 : AddMonoidAlgebra.coeff (A (mono K k d g) : MvPolynomial (Fin k) K) m ≠ 0 := right_ne_zero_of_mul h
    refine ⟨degree_of_coeff_ne _ h2, ?_⟩
    by_contra hg
    have h0 : mono K k d g = 0 := by
      unfold mono
      rw [dite_eq_right hg]
    rw [h0, map_zero] at h2
    simp at h2
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩ <;> rw [mem_weightedHomogeneousSubmodule] <;> intro n hn <;>
    obtain ⟨m, g, rfl⟩ := exists_sumElim n
  · rw [weight_wx]
    exact (key m g hn).1
  · rw [weight_wxi]
    exact (key m g hn).2

theorem symbolMapMulLeft : KappaLeft := by
  intro K _ _ k d a b A
  set_option synthInstance.maxHeartbeats 100000 in
    rw [kappa_apply, kappa_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mul_apply_eq_comp, Ed_val, Derivation.map_smul, mul_smul_comm]
  congr 1
  simp only [Derivation.leibniz, pderiv_inl_xi, smul_eq_mul]
  rw [pderiv_rename Sum.inl_injective, map_mul, rename_X]
  ring

private theorem coeff_pderiv_eq_coeff_add_single_mul_multinomial_depth {σ : Type} {K : Type} [Field K] (i : σ) (P : MvPolynomial σ K)
    (n : σ →₀ ℕ) : AddMonoidAlgebra.coeff (pderiv i P) n = AddMonoidAlgebra.coeff P (n + Finsupp.single i 1) * ((n i : K) + 1) := by
  classical
  induction P using MvPolynomial.induction_on'
  next u c =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : u = n + Finsupp.single i 1
    · subst h
      simp
    · rw [ite_eq_right h, zero_mul]
      split_ifs with h2
      · have hu : u i = 0 := by
          by_contra hne
          apply h
          rw [← h2, tsub_add_cancel_of_le]
          rw [Finsupp.single_le_iff]
          omega
        simp [hu]
      · rfl
  next p q hp hq =>
    rw [map_add (f := _), AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Finsupp.add_apply, hp, hq, add_mul]

theorem symbolMapMulRight : KappaRight := by
  intro K _ _ k d a b A
  apply pol_ext
  intro m g
  rw [coeff_kappa, mul_apply_eq_comp, Ed_mono, map_smul, Submodule.coe_smul, coeff_smul, coeff_X_mul']
  by_cases hb : g b = 0
  · rw [ite_eq_right (by simp [hb])]
    simp [hb]
  · rw [ite_eq_left (by simp [hb]), sumElim_sub_single_inr, coeff_pderiv_eq_coeff_add_single_mul_multinomial_depth, sumElim_add_single_inr, coeff_kappa]
    simp only [Finsupp.sumElim_apply, Sum.elim_inr]
    have h1 := invFact_add_single (K := K) (g - single b 1) a
    have h2 := invFact_add_single (K := K) (g - single b 1) b
    have hle : single b 1 ≤ g := by
      rw [Finsupp.single_le_iff]
      omega
    rw [tsub_add_cancel_of_le hle] at h2
    have h3 : ((g - single b 1 : Fin k →₀ ℕ) b : K) + 1 = (g b : K) := by
      have h4 : (g - single b 1 : Fin k →₀ ℕ) b + 1 = g b := by
        simp
        omega
      exact_mod_cast h4
    rw [h3] at h2
    linear_combination (AddMonoidAlgebra.coeff (A (mono K k d (g - single b 1 + single a 1)) : MvPolynomial (Fin k) K) m) * h2 -
      (AddMonoidAlgebra.coeff (A (mono K k d (g - single b 1 + single a 1)) : MvPolynomial (Fin k) K) m) * h1

private theorem coeff_sumElim_tt_pow (K : Type) [Field K] (k d : ℕ) (m g : Fin k →₀ ℕ) :
    AddMonoidAlgebra.coeff (tt K k ^ d) (Finsupp.sumElim m g) =
      if m = g ∧ g.degree = d then ((Nat.multinomial Finset.univ ⇑g : ℕ) : K) else 0 := by
  classical
  have hprod : ∀ f : Fin k → ℕ, ∏ i, (X (Sum.inl i) * X (Sum.inr i) : Pol K k) ^ f i =
      monomial (Finsupp.sumElim (Finsupp.equivFunOnFinite.symm f) (Finsupp.equivFunOnFinite.symm f)) 1 := by
    intro f
    rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
    simp [mul_pow, Finset.prod_mul_distrib]
  rw [tt, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]
  simp only [hprod, ← map_natCast (C : K →+* Pol K k), coeff_C_mul, coeff_monomial, sumElim_inj, mul_ite,
    mul_one, mul_zero]
  by_cases h : m = g ∧ g.degree = d
  · obtain ⟨hmg, hd⟩ := h
    rw [ite_eq_left ⟨hmg, hd⟩, Finset.sum_eq_single (⇑g)]
    · simp [hmg]
    · intro f _ hf
      rw [ite_eq_right]
      rintro ⟨_, h2⟩
      apply hf
      rw [← h2]
      simp
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_piAntidiag]
      refine ⟨?_, fun i _ => Finset.mem_univ i⟩
      rw [← hd, Finsupp.degree_eq_sum]
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun f hf => ?_
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    apply h
    refine ⟨h1.symm.trans h2, ?_⟩
    rw [← h2, Finsupp.degree_eq_sum]
    have h3 := (Finset.mem_piAntidiag.1 hf).1
    simpa using h3

theorem symbolMapOne : KappaId := by
  intro K _ _ k d
  apply pol_ext
  intro m g
  rw [coeff_kappa, one_apply_eq_self, mono_val, coeff_smul, smul_eq_mul, coeff_sumElim_tt_pow]
  by_cases h : m = g ∧ g.degree = d
  · obtain ⟨hmg, hd⟩ := h
    rw [ite_eq_left hd, ite_eq_left ⟨hmg, hd⟩, coeff_monomial, ite_eq_left hmg.symm, mul_one]
    have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin k)) ⇑g
    have hsum : ∑ i, g i = d := by rw [← hd, Finsupp.degree_eq_sum]
    rw [hsum] at hspec
    have hcast : ((d.factorial : ℕ) : K) =
        (∏ i, ((g i).factorial : K)) * (Nat.multinomial Finset.univ ⇑g : K) := by
      exact_mod_cast hspec.symm
    have hM : (Nat.multinomial Finset.univ ⇑g : K) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hcast
      exact (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero d)) hcast
    unfold invFact
    rw [prodFact_fintype, hcast, mul_inv, mul_assoc, inv_mul_cancel₀ hM, mul_one]
  · rw [ite_eq_right h, mul_zero]
    split_ifs with hd
    · rw [coeff_monomial, ite_eq_right (fun hgm => h ⟨hgm.symm, hd⟩), mul_zero]
    · simp

end PI.OpWords
