module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliTransportUnitaryConj
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_transport_unitary_conj : PI.UnitaryGroupMassFormula.CapelliEig.CapTransport := by
  first | exact @GlobalTheory.capelli_transport_conj | exact GlobalTheory.capelli_transport_conj | (intros; apply GlobalTheory.capelli_transport_conj <;> assumption)
