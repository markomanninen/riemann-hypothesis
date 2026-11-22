module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Formalism.ConjugateSelfDual.Statement

@[expose] public section

namespace GlobalTheory.PadicInversePower

open Formalism.ConjugateSelfDual

theorem natCast_isUnit_padicInt (l : ℕ) [Fact (Nat.Prime l)] (n : ℕ) (h : ¬ l ∣ n) : IsUnit (n : ℤ_[l]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h

theorem inv_pow_mem (l : ℕ) [Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) (e r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    (((x : ZMod (l ^ r)).val : Qbar l) ^ e)⁻¹ ∈ c.O := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h0 : (x : ZMod (l ^ 0)).val = 0 := by
      haveI : NeZero (l ^ 0) := ⟨by simp⟩
      exact Nat.lt_one_iff.mp (by simpa only [pow_zero] using ZMod.val_lt (x : ZMod (l ^ 0)))
    rw [h0]
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp only [pow_zero, inv_one]; exact c.O.one_mem
    · simp only [Nat.cast_zero, zero_pow he.ne', inv_zero]; exact c.O.zero_mem
  · let n := (x : ZMod (l ^ r)).val
    have hcop : l.Coprime n :=
      (ZMod.val_coe_unit_coprime x).symm.of_dvd_left (dvd_pow_self l hr.ne')
    have hnd : ¬ l ∣ n := (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop
    obtain ⟨u, hu⟩ := (natCast_isUnit_padicInt l n hnd).pow e
    have key : ((n : Qbar l) ^ e)⁻¹ = algebraMap ℤ_[l] (Qbar l) ↑u⁻¹ := by
      rw [map_units_inv (algebraMap ℤ_[l] (Qbar l)) u, hu, map_pow, map_natCast]
    rw [key]
    exact c.O.algebraMap_mem _

end GlobalTheory.PadicInversePower
