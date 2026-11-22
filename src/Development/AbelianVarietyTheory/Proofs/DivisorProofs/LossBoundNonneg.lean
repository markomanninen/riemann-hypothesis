module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLossDegreeBounds
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.LocalRingCardinality.DataMink
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OneLeLetterBlockLength
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOneIdealIffAdditiveValuationPos
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

@[expose] public section

noncomputable section

namespace GlobalTheory.LossItemsCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.HCEntries

section Programme

variable {l d : ℕ} [NeZero d]

end Programme

section Point

variable {D : D7} {L : SizeData₂ D} {X : ErrX D} {K : Consts} {c : ErrC}

theorem cube_le_eta (P : ParameterChoice' D L) : 4 * (D.R.N D.R.m : ℝ) ^ 3 + 6 ≤ L.etaSz := by
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have a1 := P.h0_ge.2.2.2.2.1
  have a2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self L.etaSz_pos.le hm
  linarith [one_le_letterBlockLength D]

end Point

section Family

variable {eps : ℝ} (Fm : FamP eps)

end Family

end GlobalTheory.LossItemsCompare

end
