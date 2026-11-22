module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed

@[expose] public section

open TensorProduct Module

namespace GlobalTheory.GaloisDescent

section Decomposition

variable {ι M M' σ τ : Type*} [DecidableEq ι] [AddCommMonoid M] [AddCommMonoid M']
  [SetLike σ M] [AddSubmonoidClass σ M] [SetLike τ M'] [AddSubmonoidClass τ M']

end Decomposition

section Ideals

variable {K L A B G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A]
  [Algebra K B] [Algebra L B] [IsScalarTower K L B] {j : A →ₐ[K] B}

theorem ideal_map_comap_of_span (I : Ideal B) (N : Submodule K A)
    (h : Submodule.span L (j.toLinearMap '' N) = I.restrictScalars L) :
    (I.comap j).map j = I := by
  refine le_antisymm Ideal.map_comap_le fun x hx => ?_
  have hle : Submodule.span L (j.toLinearMap '' N) ≤ ((I.comap j).map j).restrictScalars L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    refine Ideal.mem_map_of_mem j ?_
    exact h.le (Submodule.subset_span ⟨a, ha, rfl⟩)
  exact hle (h.ge hx)

theorem ideal_map_comap_of_stable (hj : IsBaseChange L j.toLinearMap) (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (φ : G → B →+ B) (hφ : ∀ g l a, φ g (l • j a) = s g l • j a)
    (I : Ideal B) (hI : ∀ g, ∀ x ∈ I, φ g x ∈ I) : (I.comap j).map j = I :=
  ideal_map_comap_of_span I _ (span_image_comap_eq hj s hs φ hφ (I.restrictScalars L) hI)

section Graded

variable {ι σ τ : Type*} [DecidableEq ι] [AddMonoid ι] [SetLike σ A] [AddSubmonoidClass σ A]
  [SetLike τ B] [AddSubmonoidClass τ B] (𝒜 : ι → σ) (ℬ : ι → τ) [GradedRing 𝒜] [GradedRing ℬ]

end Graded

end Ideals

section Tensor

open Algebra.TensorProduct

variable {K L A G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]

end Tensor

section Polynomial

open MvPolynomial

variable {K L G σ : Type*} [Field K] [Field L] [Algebra K L]


end Polynomial

end GlobalTheory.GaloisDescent
