module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagPivotIdentity
public import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagPivot

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

section

variable (F : Type) [Field F] (n : ℕ)

abbrev PivotIdx := Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b}

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
