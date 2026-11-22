module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FormsStableOfTgtEq
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainUOperatorCommutationOfPointPairLaw
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExtInOfValIn
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfStability
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TupleChainSharpColumnValuationOfTwisted
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WtBoundsOfNonneg

@[expose] public section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section
namespace GlobalTheory.LvT.TwColumn

variable {D : D7} {u : D.what₂.Word}

def WtSigns (X : Ch D u) : Prop :=
  (∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ) ∧ ∀ i, i < D.R.m → ∀ τ, 0 ≤ X.C.sDiv i τ

end GlobalTheory.LvT.TwColumn
