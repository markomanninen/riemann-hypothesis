module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace GlobalTheory.Published

def EssSquareIntegrableSegments : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (δ : IrrGL (k := k)), 1 ≤ δ.1 →
    ((∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsSqIntCoeff (δ.tw χ hχ).rep) ↔ ∃ Δ : Segment k, IsLSeg Δ δ.rep)

namespace EssSquareIntegrableSegments

open MeasureTheory

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


end EssSquareIntegrableSegments

end GlobalTheory.Published
