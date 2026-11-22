module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeLieWordNormBound
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists

@[expose] public section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKType_lieWord_normBound : LieBound := by
  first | exact @GlobalTheory.SepReal.lieBound | exact GlobalTheory.SepReal.lieBound | (intros; apply GlobalTheory.SepReal.lieBound <;> assumption)
