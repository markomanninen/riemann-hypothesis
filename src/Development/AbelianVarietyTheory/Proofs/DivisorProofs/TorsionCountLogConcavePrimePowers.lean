module

public import Mathlib

@[expose] public section

open NumberField

namespace GlobalTheory

def killedBy {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (I : Ideal R) :
    AddSubgroup M where
  carrier := {x | ∀ a ∈ I, a • x = 0}
  zero_mem' := fun a _ => smul_zero a
  add_mem' := fun hx hy a ha => by rw [smul_add, hx a ha, hy a ha, add_zero]
  neg_mem' := fun hx a ha => by rw [smul_neg, hx a ha, neg_zero]

theorem card_eq_card_ker_mul_card_range {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) : Nat.card G = Nat.card f.ker * Nat.card f.range := by
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]

end GlobalTheory
