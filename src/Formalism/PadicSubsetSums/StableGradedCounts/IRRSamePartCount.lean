module

public import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeToPartEqIff

@[expose] public section

open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem lpow_order_iff {G : Type*} [Monoid G] {l n : ℕ} (hl : l.Prime) (hn : n ≠ 0) (z : G)
    (hz : z ^ n = 1) : (∃ a : ℕ, z ^ (l ^ a) = 1) ↔ z ^ (l ^ padicValNat l n) = 1 := by
  constructor
  · rintro ⟨a, ha⟩
    have hg : z ^ (l ^ a).gcd n = 1 := pow_gcd_eq_one.2 ⟨ha, hz⟩
    obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow hl).1 (Nat.gcd_dvd_left (l ^ a) n)
    have hkn : l ^ k ∣ n := by
      rw [← hk']
      exact Nat.gcd_dvd_right _ _
    haveI := Fact.mk hl
    have hkv : k ≤ padicValNat l n := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hn).1 hkn
    obtain ⟨c, hc⟩ := pow_dvd_pow l hkv
    rw [hc, pow_mul, ← hk', hg, one_pow]
  · intro h
    exact ⟨_, h⟩

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
