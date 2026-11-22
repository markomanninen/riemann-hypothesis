module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIwasawaCellsDisjoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwasawa_cells_disjoint : CosetInj := by
  first | exact @GlobalTheory.InertZeta.cosetInj | exact GlobalTheory.InertZeta.cosetInj | (intros; apply GlobalTheory.InertZeta.cosetInj <;> assumption)
