module

public import Mathlib
public import Formalism.PeriodIntegrals.RowWtSpan
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowWeightSpan.RowWtSpanOfBideterminant

@[expose] public section

theorem rowWtSpan_of (h1 : PI.RW.BideterminantMem) (h2 : PI.RW.BideterminantSpan) : PI.RowWtSpan :=
  PI.RWS.rowWtSpan_of_bideterminant h1 h2
