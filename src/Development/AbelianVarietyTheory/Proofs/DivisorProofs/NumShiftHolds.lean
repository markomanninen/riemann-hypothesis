module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.BlockCombStatement

@[expose] public section

namespace GlobalTheory.PsCo.PcEG

theorem numShift_holds (n : ℕ) (ε : Fin n → Bool) (m : Fin n → ℤ) (c : Bool → ℤ)
    (t : Fin n → ℂ) (ht : ∀ a, t a ≠ 0) :
    ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε (fun a => m a - c (ε a)) t =
      (∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ε ∘ w = ε),
        ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, t a ^ m (w.symm a)) * ∏ a, t a ^ (-c (ε a)) := by
  delta ReciprocityTheory.ChartRestriction.TR.Weyl.numK
  have hfilt : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, ε (σ i) = ε i)) =
      Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ε ∘ w = ε) := by
    ext w; simp [funext_iff]
  rw [hfilt, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw' : ∀ i, ε (w i) = ε i := fun i => congrFun (Finset.mem_filter.1 hw).2 i
  rw [mul_assoc]
  congr 1
  have h1 : ∏ i, t (w i) ^ (m i - c (ε i)) =
      (∏ i, t (w i) ^ m i) * ∏ i, t (w i) ^ (-c (ε (w i))) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hw', sub_eq_add_neg, zpow_add₀ (ht _)]
  rw [h1]
  congr 1
  · have := Equiv.prod_comp w (fun a => t a ^ m (w.symm a))
    simpa using this
  · exact Equiv.prod_comp w (fun a => t a ^ (-c (ε a)))

end GlobalTheory.PsCo.PcEG
