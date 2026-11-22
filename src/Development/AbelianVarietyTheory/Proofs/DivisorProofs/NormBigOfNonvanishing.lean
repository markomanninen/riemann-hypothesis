module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLFunctionBottomPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankSumLeHalfRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdMassNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockIpSelfRePos
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacNormNeZero

@[expose] public section

open Finset
open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum
open GlobalTheory.NormSum (Pair)
open GlobalTheory.CMVal (IsHeckeL)

namespace GlobalTheory.NormBigProof

theorem squareBottomHalfRankSum_le_halfRank (D : Formalism.BasicNotions.D7) (i j : ℕ) : h0 D i j ≤ halfRank D i j := by
  unfold h0 halfRank botBig botSmall
  exact Nat.div_le_div_right (Nat.add_le_add (Nat.sub_le _ _) (Nat.sub_le _ _))

end GlobalTheory.NormBigProof
