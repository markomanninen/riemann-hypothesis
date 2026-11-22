module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.Core.Rk



def BigGap (D : D7) : Prop := D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6)

def IsScaleWithBoundedGamma (D : D7) (L C' : ℝ) : Prop := ∃ large₂ : SizeData₂ D, large₂.sc.L = L ∧ 8 * large₂.CGam ≤ C' ∧ 1 ≤ large₂.CGam

end GlobalTheory.Core.Rk

end
