module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NablaPowApplySmulLeibniz
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nabla_pow_apply_smul_leibniz : ∀ {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι), (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1), (k.choose p : K⟦X⟧) • ((fun τ => (⇑(PowerSeries.derivative (R := K)))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  intro O K _ _ _ _ _ l e a ι _ _ P C k f v
  let D (p : ℕ) (τ : ZMod a) := (⇑(PowerSeries.derivative (R := K)))^[p] (f τ)
  have h (n : ℕ) : (C.nabla ^ n) (f • v) = ∑ p ∈ Finset.range (n + 1),
      n.choose p • (D p • (C.nabla ^ (n - p)) v) := by
    induction n with
    | zero => simp [D]
    | succ n ih =>
      rw [Finset.sum_choose_succ_nsmul (fun i j => D i • (C.nabla ^ j) v) n,
        pow_succ', mul_apply_eq_comp, ih, map_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpn : p ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
      rw [map_nsmul, C.leibniz, smul_add, add_comm]
      congr 2
      · rw [show n + 1 - p = n - p + 1 by omega, pow_succ', mul_apply_eq_comp]
      · congr 1
        funext τ
        exact (Function.iterate_succ_apply' _ _ _).symm
  rw [h k]
  exact Finset.sum_congr rfl fun p _ => (Nat.cast_smul_eq_nsmul K⟦X⟧ _ _).symm
