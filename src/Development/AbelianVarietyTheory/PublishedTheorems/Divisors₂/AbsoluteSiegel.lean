module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt

@[expose] public section

open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt

namespace GlobalTheory.Published

def ConjInv {K : Type} [Field K] {m : ℕ} (h : HermFam K (Fin m → K)) : Prop :=
  ∀ (σ : K →+* ℂ) x y, h.form ((starRingEnd ℂ).comp σ) x y = starRingEnd ℂ (h.form σ x y)

end GlobalTheory.Published
