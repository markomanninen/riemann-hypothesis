module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.MapEqPadicPowCyclotomicCharacter

@[expose] public section

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v

section Poly

variable {A : Type u} [CommRing A]

theorem eq_C_of_derivative_eq_zero (h : ∀ n : ℕ, IsUnit ((n : A) + 1)) {f : Polynomial A}
    (hf : Polynomial.derivative f = 0) : f = Polynomial.C (f.coeff 0) := by
  ext n
  rcases n with _ | n
  · simp
  · have h1 := Polynomial.coeff_derivative f n
    rw [hf, Polynomial.coeff_zero] at h1
    rw [Polynomial.coeff_C_succ]
    exact (h n).mul_left_eq_zero.1 h1.symm

end Poly

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

open tateModule

theorem Acris.logTeich_padicPow (η : tateModule p R) (a : ℤ_[p]) :
    Acris.logTeich (padicPow η a) = algebraMap ℤ_[p] (Acris p R) a * Acris.logTeich η := by
  rw [← sub_eq_zero]
  refine Acris.eq_zero_of_forall_dvd fun k => ?_
  have h := Ideal.mem_span_singleton.1 (PadicInt.appr_spec k a)
  obtain ⟨η', hη'⟩ := exists_padicPow_eq η h
  obtain ⟨b, hb⟩ := h
  refine ⟨Acris.logTeich η' - algebraMap ℤ_[p] (Acris p R) b * Acris.logTeich η, ?_⟩
  have ha : algebraMap ℤ_[p] (Acris p R) a =
      (a.appr k : Acris p R) + (p : Acris p R) ^ k * algebraMap ℤ_[p] (Acris p R) b := by
    conv_lhs => rw [← sub_add_cancel a (a.appr k), hb]
    rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast, add_comm]
  rw [hη', Acris.logTeich_mul, Acris.logTeich_pow, Acris.logTeich_pow, ha, Nat.cast_pow]
  ring


theorem Bcris.algebraMap_padicInt (a : ℤ_[p]) :
    algebraMap ℚ_[p] (Bcris p R) a =
      algebraMap (Acris p R) _ (algebraMap ℤ_[p] (Acris p R) a) :=
  congrArg (algebraMap (BcrisPlus p R) (Bcris p R)) (BcrisPlus.algebraMap_padicInt a)

section Good

variable [IsDomain R] [ValuationRing R] [IsAlgClosed (FractionRing R)] [CharZero R]

variable (p R)


variable {p R}

end Good

namespace Bst

open Polynomial

variable [IsDomain R] [CharZero R] [ValuationRing R]

variable [IsAlgClosed (FractionRing R)]




variable (p R) in
def u : Bst p R := logFlat (pflat (p := p) (R := R))

end Bst

end Reformulated.AutPerF
