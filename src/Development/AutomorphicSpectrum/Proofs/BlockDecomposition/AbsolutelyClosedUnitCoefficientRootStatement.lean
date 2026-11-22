module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsolutelyClosedUnitCoefficientRoot
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

@[expose] public section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
open Polynomial in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolutely_closed_unit_coefficient_root :
    ∀ {S : Type} [CommRing S], Aic (S := S) →
      (∀ a b : S, IsUnit (a + b) → IsUnit a ∨ IsUnit b) →
      ∀ (Q : Polynomial S) (i : ℕ), Q.coeff 0 = 1 → 0 < i → IsUnit (Q.coeff i) →
        ∃ y, Q.eval y = 0 := by
  intro S _ hA hL Q i h0 hi hu
  rcases subsingleton_or_nontrivial S with hs | hn
  · exact ⟨0, Subsingleton.elim _ _⟩
  have : IsLocalRing S := IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add hL
  have htd : Q.natTrailingDegree = 0 :=
    Nat.le_zero.mp (natTrailingDegree_le_of_ne_zero (by rw [h0]; exact one_ne_zero))
  have hmon : Q.reverse.Monic := by
    rw [Monic, reverse_leadingCoeff, trailingCoeff, htd, h0]
  have hdeg : Q.reverse.natDegree = Q.natDegree := by
    rw [reverse_natDegree, htd, Nat.sub_zero]
  have hid : i ≤ Q.natDegree := le_natDegree_of_ne_zero hu.ne_zero
  obtain ⟨s, hs⟩ := GlobalTheory.T.absolutely_closed_polynomial_splits hA _ hmon
  by_cases hex : ∃ b ∈ s, IsUnit b
  · obtain ⟨b, hbs, hb⟩ := hex
    have hroot : Q.reverse.eval b = 0 := by
      have hdvd : (X : S[X]) - C b ∣ Q.reverse := by
        rw [hs]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hbs)
      exact dvd_iff_isRoot.mp hdvd
    obtain ⟨u, rfl⟩ := hb
    refine ⟨((u⁻¹ : Sˣ) : S), ?_⟩
    let : Invertible ((u⁻¹ : Sˣ) : S) := (u⁻¹).invertible
    have key := eval₂_reverse_mul_pow (RingHom.id S) ((u⁻¹ : Sˣ) : S) Q
    have hinv : ⅟((u⁻¹ : Sˣ) : S) = (u : S) := by simp
    rw [hinv, eval₂_id, eval₂_id, hroot, zero_mul] at key
    exact key.symm
  · exfalso
    let m := IsLocalRing.maximalIdeal S
    have coeff_prod_mem (t : Multiset S) (ht : ∀ b ∈ t, b ∈ m) :
        ∀ k < t.card, ((t.map fun b => (X : S[X]) - C b).prod).coeff k ∈ m := by
      induction t using Multiset.induction_on with
      | empty => intro k hk; simp at hk
      | cons a t ih =>
        intro k hk
        have ha := ht a (Multiset.mem_cons_self a t)
        have ih' := ih fun b hb => ht b (Multiset.mem_cons_of_mem hb)
        rw [Multiset.map_cons, Multiset.prod_cons, sub_mul]
        rw [Multiset.card_cons] at hk
        cases k with
        | zero =>
          simp only [coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub]
          exact m.neg_mem (m.mul_mem_right _ ha)
        | succ k =>
          simp only [coeff_sub, coeff_X_mul, coeff_C_mul]
          exact m.sub_mem (ih' k (by omega)) (m.mul_mem_right _ ha)
    have hall : ∀ b ∈ s, b ∈ m := fun b hb =>
      (IsLocalRing.mem_maximalIdeal b).mpr fun hbu => hex ⟨b, hb, hbu⟩
    have hcard : s.card = Q.natDegree := by
      rw [← hdeg, hs, natDegree_multiset_prod_X_sub_C_eq_card]
    have hcoeff : Q.reverse.coeff (Q.natDegree - i) = Q.coeff i := by
      rw [coeff_reverse, revAt_le (Nat.sub_le _ _)]
      congr 1
      omega
    have hmem := coeff_prod_mem s hall (Q.natDegree - i) (by omega)
    rw [← hs, hcoeff] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu
