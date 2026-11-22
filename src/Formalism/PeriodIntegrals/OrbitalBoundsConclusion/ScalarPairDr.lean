module

public import Mathlib
public import Formalism.PeriodIntegrals.ScalarPairDr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.ExistsNeZeroMem

@[expose] public section

theorem scalar_pair_dr (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : PI.ScalarPairDr.ScalarDr D u u' :=
  PI.ScalarPairDr.W.scalarDr D u u'
