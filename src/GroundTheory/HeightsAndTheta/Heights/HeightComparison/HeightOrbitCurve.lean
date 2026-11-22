module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightObjects

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def OrbitCurve.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (x : Cone n (AlgebraicClosure ℚ)), BlockNonzero x →
    Geo.IsArithVar (ι := blockIdx n) (orbitIdeal x) 1

end GroundTheory.Heights₂.Heights
