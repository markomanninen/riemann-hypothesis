module

public import Mathlib

@[expose] public section

namespace GlobalTheory.Morita

structure MatrixUnits (R : Type*) [CommRing R] (N : Type*) [AddCommGroup N] [Module R N]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where

  E : ι → ι → Module.End R N
  mul_eq : ∀ i j k l, E i j * E k l = if j = k then E i l else 0
  sum_diag : ∑ i, E i i = 1

variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace MatrixUnits

variable (U : MatrixUnits R N ι)

theorem apply_apply (i j k l : ι) (x : N) : U.E i j (U.E k l x) = if j = k then U.E i l x else 0 := by
  have h := LinearMap.congr_fun (U.mul_eq i j k l) x
  rw [Module.End.mul_apply] at h
  rw [h]; split_ifs <;> simp

theorem sum_apply (x : N) : ∑ i, U.E i i x = x := by
  have h := LinearMap.congr_fun U.sum_diag x
  simpa [LinearMap.sum_apply] using h

def corner (a : ι) : Submodule R N := LinearMap.range (U.E a a)

theorem mem_corner_iff (a : ι) (x : N) : x ∈ U.corner a ↔ U.E a a x = x := by
  constructor
  · rintro ⟨y, rfl⟩; rw [U.apply_apply]; simp
  · intro h; exact ⟨x, h⟩

theorem apply_mem_corner (a i : ι) (x : N) : U.E a i x ∈ U.corner a := ⟨U.E a i x, by rw [U.apply_apply]; simp⟩

def toPi (a : ι) : N ≃ₗ[R] (ι → U.corner a) where
  toFun x i := ⟨U.E a i x, U.apply_mem_corner a i x⟩
  map_add' x y := by ext i; simp
  map_smul' r x := by ext i; simp
  invFun v := ∑ i, U.E i a (v i)
  left_inv x := by
    simp only
    conv_rhs => rw [← U.sum_apply x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [U.apply_apply]; simp
  right_inv v := by
    ext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, U.apply_apply]
    simp [(U.mem_corner_iff a _).1 (v j).2]

theorem toPi_apply (a : ι) (x : N) (i : ι) : ((U.toPi a x) i : N) = U.E a i x := rfl

theorem toPi_E (a i j : ι) (x : N) : U.toPi a (U.E i j x) = Pi.single i (U.toPi a x j) := by
  ext k
  rw [toPi_apply, U.apply_apply]
  by_cases h : k = i
  · subst h; simp [toPi_apply]
  · simp [h, Pi.single_apply]

end MatrixUnits

def stdUnits (M : Type*) [AddCommGroup M] [Module R M] : MatrixUnits R (ι → M) ι where
  E i j := LinearMap.single R (fun _ => M) i ∘ₗ LinearMap.proj j
  mul_eq i j k l := by
    ext x m
    by_cases h : j = k
    · subst h; simp [Pi.single_apply]
    · simp [h, Pi.single_apply]
  sum_diag := by
    ext x m
    simp [LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]

end GlobalTheory.Morita

namespace GlobalTheory.Morita
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

end GlobalTheory.Morita

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

section semilinear

variable {σ : R →+* R} (F : N →ₛₗ[σ] N)

end semilinear

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

section extend

variable {σ : R →+* R}

def extend (a : ι) (F₀ : U.corner a →ₛₗ[σ] U.corner a) : N →ₛₗ[σ] N where
  toFun x := ∑ i, U.E i a (F₀ (U.toPi a x i))
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum]

end extend

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

end GlobalTheory.Morita

namespace GlobalTheory.Morita
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]

end GlobalTheory.Morita

universe w

namespace GlobalTheory.Morita

variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]


end GlobalTheory.Morita
