module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ValuationCompositionDivisor

theorem valR_comp {A : Type} [CommRing A] {X Y : Scheme.{0}} (p : Sp A ⟶ X) (ψ : X ⟶ Y)
    (U : Y.Opens) (f : Γ(Y, U)) :
    valR (p ≫ ψ) U f = valR p (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) := by
  unfold valR
  rfl

end GlobalTheory.ValuationCompositionDivisor
