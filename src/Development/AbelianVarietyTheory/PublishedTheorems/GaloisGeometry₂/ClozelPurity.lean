module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.Published

def ClozelPurity : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a,
    (∀ τ, ∀ z ∈ (CG.mk π).infChar τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) →
    ∃ w₀ : ℤ, ∀ τ : E →+* ℂ,
      (CG.mk π).infChar ((starRingEnd ℂ).comp τ) = ((CG.mk π).infChar τ).map fun z => (w₀ : ℂ) - z

end GlobalTheory.Published

end
