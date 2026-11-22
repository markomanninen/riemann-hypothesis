module

public import Formalism.FockGram.StatementFock

@[expose] public section

open Finset MvPolynomial

namespace Formalism.E

section
variable {R τ : Type*} [CommRing R] [StarRing R]

theorem fock_eq_sum_of_subset (f g : MvPolynomial τ R) (s : Finset (τ →₀ ℕ))
    (h : f.support ⊆ s) :
    fock f g = ∑ m ∈ s, f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R) := by
  classical
  unfold fock
  refine Finset.sum_subset h ?_
  intro m _ hm
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]

theorem fock_add_left (f f' g : MvPolynomial τ R) : fock (f + f') g = fock f g + fock f' g := by
  classical
  rw [fock_eq_sum_of_subset (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    fock_eq_sum_of_subset f g (f.support ∪ f'.support) Finset.subset_union_left,
    fock_eq_sum_of_subset f' g (f.support ∪ f'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_add]; ring)

end

end Formalism.E
