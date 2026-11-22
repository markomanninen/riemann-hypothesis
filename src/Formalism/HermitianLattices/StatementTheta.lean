module

public import Mathlib
public import Formalism.LatticeTheta.Statement
public import Formalism.HermitianLattices.StatementLat

@[expose] public section

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Defs

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

def thetaL (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) (γ : V)
    (τ : ℂ) : ℂ :=
  ∑' x : L, Complex.exp (Real.pi * Complex.I * τ *
    ((Algebra.trace ℚ K (h (γ + x) (γ + x)) : ℚ) : ℂ))

end Defs

end Formalism.HermitianLatticesTheory
