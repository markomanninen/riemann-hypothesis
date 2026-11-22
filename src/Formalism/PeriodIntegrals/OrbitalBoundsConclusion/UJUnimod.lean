module

public import Formalism.PeriodIntegrals.UJUnimod
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

@[expose] public section

theorem unitary_unimodular_right_inv : PI.UJUnimod.UJRightInv :=
  fun n ε => ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
