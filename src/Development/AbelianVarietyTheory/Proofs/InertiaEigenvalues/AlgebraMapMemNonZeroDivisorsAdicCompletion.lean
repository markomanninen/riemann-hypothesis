module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap

@[expose] public section

namespace GlobalTheory.BK

open PowerSeries Filter Topology

theorem algebraMap_mem_nonZeroDivisors_adicCompletion {B : Type} [CommRing B] {s : B}
    (hs : s ∈ nonZeroDivisors B) :
    algebraMap B (AdicCompletion (Ideal.span {s}) B) s ∈
      nonZeroDivisors (AdicCompletion (Ideal.span {s}) B) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {s}) (n + 1) x)
  have h1 := congrArg (AdicCompletion.evalₐ (Ideal.span {s}) (n + 1)) hx
  rw [map_mul, map_zero, AlgHom.commutes, ← hr, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 : (r - s ^ n * c) * s = 0 := by rw [sub_mul, hc]; ring
  have h3 := (mem_nonZeroDivisors_iff_right.1 hs) _ h2
  rw [evalₐ_of_succ _ hr.symm, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact ⟨c, sub_eq_zero.1 h3⟩

theorem Ehat_mem_nonZeroDivisors (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] : Ehat O K l e ∈ nonZeroDivisors (Ahat O K l e) := by
  have hE : E (K := K) l e ≠ 0 := by
    intro h
    have hcoeff := congrArg (coeff e) h
    rw [E, map_add, coeff_X_pow_self, ← map_natCast (C : K →+* K⟦X⟧),
      coeff_C_of_ne_zero (NeZero.ne e), add_zero, map_zero] at hcoeff
    exact one_ne_zero hcoeff
  let s : invL l (A O K) :=
    ⟨E (K := K) l e, by
      unfold E
      exact add_mem (pow_mem HasU.X_mem e) (natCast_mem _ l)⟩
  exact algebraMap_mem_nonZeroDivisors_adicCompletion (s := s)
    (mem_nonZeroDivisors_of_ne_zero fun h => hE (congrArg Subtype.val h))

end GlobalTheory.BK
