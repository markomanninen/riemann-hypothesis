module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsSquareIntegrable

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.Published

def SquareIntegrableSegment : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (δ : IrrGL (k := k)), UnitaryDual.IsSquareIntegrable δ → ∃ Δ : Segment k, IsLSeg Δ δ.rep

end GlobalTheory.Published

end
