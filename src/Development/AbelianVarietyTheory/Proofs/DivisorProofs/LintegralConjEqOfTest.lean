module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CoeConjEquivSymm

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine

def conjNormalEquiv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) (b : G) (h : ∀ u, u ∈ N ↔ b * u * b⁻¹ ∈ N) : N ≃ₜ* N := GlobalTheory.ConjugationEquiv.conjEquiv N b h

end GlobalTheory.ResLine
