module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace Domination

section Charts

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}

theorem chartRing_eq_ampleBase {i : Fin (N + 1)} (hi : x i ≠ 0) :
    chartRing (S := S) (x := x) (singleChart hi) = ampleBase (S := S) x i := by
  apply le_antisymm
  · intro a ha
    have := (algebraMap S Ω).domain_nontrivial
    obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
    change s ∈ monos {i} at hs
    have hs' : s ∈ Submonoid.closure ({X i} : Set (Poly S N)) := by
      simpa [monos] using hs
    obtain ⟨m, rfl⟩ := Submonoid.mem_closure_singleton.mp hs'
    have hm : e = m := hse.inj_right (isHomogeneous_X_pow i m) (by
      rw [X_pow_eq_monomial, Ne, monomial_eq_zero]
      exact one_ne_zero)
    subst e
    rw [map_pow, aeval_X, ← aeval_div_of_isHomogeneous hf i, ampleBase,
      Algebra.adjoin_range_eq_range_aeval]
    exact ⟨f, rfl⟩
  · rw [ampleBase, Algebra.adjoin_le_iff]
    rintro _ ⟨l, rfl⟩
    have hXi : (X i : Poly S N) ∈ monos {i} := X_mem_monos (Finset.mem_singleton_self i)
    exact ⟨X l, X i, 1, hXi, isHomogeneous_X S l, isHomogeneous_X S i, by simp⟩

theorem isNoetherianRing_chartRing [IsNoetherianRing S] {i : Fin (N + 1)} (hi : x i ≠ 0) :
    IsNoetherianRing (chartRing (S := S) (x := x) (singleChart hi)) := by
  classical
  have hfg : (chartRing (S := S) (x := x) (singleChart hi)).FG := by
    rw [chartRing_eq_ampleBase hi, ampleBase]
    refine ⟨Finset.univ.image fun l => x l / x i, ?_⟩
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have : Algebra.FiniteType S (chartRing (S := S) (x := x) (singleChart hi)) :=
    ⟨(Subalgebra.fg_top _).mpr hfg⟩
  exact Algebra.FiniteType.isNoetherianRing S _

variable {i : Fin (N + 1)} (hi : x i ≠ 0) {j : Fin (N' + 1)} (hj : x' j ≠ 0)



end Charts

section Clauses

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N N' : ℕ}
  {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}


end Clauses

end Domination

end

end GroundTheory.Heights₂.Heights.Kleiman
