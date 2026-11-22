module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankKsEq

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

theorem padicValNat_finrank_Ks : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l), (∀ m : ℕ, 0 < m → padicValNat l (finrank ℚ_[l] ↥(Loc.Ks K m)) - padicValNat l (finrank ℚ_[l] ↥(Loc.Ks K 1)) = m - 1) ∧ (K.1 ≤ Loc.MaximalUnramifiedExtension l → padicValNat l (finrank ℚ_[l] ↥(Loc.Ks K 1)) - padicValNat l (finrank ℚ_[l] ↥K.1) = 0) := by
  intro l _ K
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl1 : l - 1 ≠ 0 := by omega
  have hpow : ∀ n : ℕ, l ^ n ≠ 0 := fun n => pow_ne_zero n (by omega)

  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hle : Loc.K0 K ≤ K.1 := by unfold Loc.K0; exact inf_le_left
  haveI : FiniteDimensional ℚ_[l] ↥(Loc.K0 K) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  have hk0 : finrank ℚ_[l] ↥(Loc.K0 K) ≠ 0 := Module.finrank_pos.ne'
  refine ⟨fun m hm => ?_, fun hK => ?_⟩
  ·
    rw [finrank_Ks_eq l K m hm, finrank_Ks_eq l K 1 one_pos,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hk0 (Nat.mul_ne_zero (hpow _) hl1),
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hk0 (Nat.mul_ne_zero (hpow _) hl1),
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (hpow _) hl1, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (hpow _) hl1,
      (show ∀ n : ℕ, padicValNat l (l ^ n) = n from fun n => by simpa only [Nat.padicValNat_def] using Nat.multiplicity_prime_pow (p := l) n),
      (show ∀ n : ℕ, padicValNat l (l ^ n) = n from fun n => by simpa only [Nat.padicValNat_def] using Nat.multiplicity_prime_pow (p := l) n)]
    omega
  ·
    have heq : Loc.K0 K = K.1 := by unfold Loc.K0; exact inf_eq_left.mpr hK
    have hK1 : finrank ℚ_[l] ↥K.1 ≠ 0 := Module.finrank_pos.ne'
    have hv : padicValNat l (l - 1) = 0 :=
      by
        apply (Nat.padicValNat_def).trans
        exact padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    rw [finrank_Ks_eq l K 1 one_pos, heq, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hK1 (Nat.mul_ne_zero (hpow _) hl1),
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (hpow _) hl1, (show ∀ n : ℕ, padicValNat l (l ^ n) = n from fun n => by simpa only [Nat.padicValNat_def] using Nat.multiplicity_prime_pow (p := l) n), hv]
    omega

end GlobalTheory.HubLoc
