module

public import Mathlib
public import Formalism.PeriodIntegrals.KerLat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PeriodPairIndependence.IndepOfImNe

@[expose] public section

theorem exists_periodPairOfIdeal : PI.KerLat.PerPair := PI.KerLat.PerPairProof.perPair
