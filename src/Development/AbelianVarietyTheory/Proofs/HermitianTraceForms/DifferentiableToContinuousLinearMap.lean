module

public import Mathlib

@[expose] public section

namespace GlobalTheory

open Module

section Defs

variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]

def isoTransvection (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0) (b : R) : M ≃ₗ[R] M :=
  LinearEquiv.transvection (f := b • h.flip x) (v := x) (by simp [hx])

namespace isoTransvection

variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)

theorem apply (b : R) (v : M) : isoTransvection h x hx b v = v + (b * h v x) • x := rfl

end isoTransvection

namespace isoTransvection

variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)

variable {h}

variable (h)

section Lattice

variable {R₀ : Type*} [CommRing R₀] [Algebra R₀ R] [Module R₀ M] [IsScalarTower R₀ R M]

end Lattice

end isoTransvection

end Defs

section Complex

namespace isoTransvection

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {h : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} (x : W)
  (hx : h x x = 0)

end isoTransvection

namespace isoTransvection

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (h : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (x : W)
  (hx : h x x = 0)

end isoTransvection

end Complex

section Example

private noncomputable def hyp : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun u v => u.1 * star v.2 + u.2 * star v.1)
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring)

end Example

end GlobalTheory
