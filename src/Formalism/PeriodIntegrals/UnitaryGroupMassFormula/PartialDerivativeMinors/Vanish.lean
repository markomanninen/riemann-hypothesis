module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

theorem list_prod_eq_mul_of_mem {M : Type} [Monoid M] (x : M) :
    ∀ l : List M, (∀ y ∈ l, Commute y x) → x ∈ l → ∃ r : M, l.prod = r * x := by
  intro l
  induction l with
  | nil =>
    intro _ hx
    exact absurd hx List.not_mem_nil
  | cons a l ih =>
    intro hc hx
    have hc' : ∀ y ∈ l, Commute y x := fun y hy => hc y (List.mem_cons_of_mem _ hy)
    rcases List.mem_cons.1 hx with h | h
    · subst a
      exact ⟨l.prod, by rw [List.prod_cons, (Commute.list_prod_left l x hc').eq]⟩
    · obtain ⟨r, hr⟩ := ih hc' h
      exact ⟨a * r, by rw [List.prod_cons, hr, mul_assoc]⟩

theorem vanish_of (hB : PBridge) (hC : PLapComm) (hZ : PLapZero) : PVanish := by
  intro H _ _ N0 N1 nu I m κ2 n t ht
  have hzero : lapAll N0 N1 n (Gxz N0 N1 nu I) = 0 := by
    obtain ⟨r, hr⟩ := list_prod_eq_mul_of_mem (lapT (H := H) N0 N1 t ^ n t)
      ((Finset.univ : Finset H).toList.map fun t => lapT N0 N1 t ^ n t)
      (fun y hy => by
        obtain ⟨t', _, rfl⟩ := List.mem_map.1 hy
        exact (hC H N0 N1 t' t).pow_pow _ _)
      (List.mem_map.2 ⟨t, Finset.mem_toList.2 (Finset.mem_univ t), rfl⟩)
    unfold lapAll
    rw [hr, mul_apply_eq_comp, hZ H N0 N1 nu I t (n t) ht, map_zero]
  have h := hB H N0 N1 (Gxz N0 N1 nu I) m κ2 n
  rw [hzero, AddMonoidAlgebra.coeff_zero] at h
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h (Finset.prod_ne_zero_iff.2 fun t' _ => by exact_mod_cast (Nat.factorial_ne_zero (n t')))
  · exact h

end PI.EntAtD.W
