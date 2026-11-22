module

public import Mathlib
public import Formalism.PeriodIntegrals.ScRefExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.TargetOfWframe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.WFrameOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.PrincipalIdealRingAtPrime
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.WeilBasisExistence

@[expose] public section

theorem sc_reference_exists : PI.ScRefExists.Target :=
  PI.ScRefExists.Top.target_of_wframe
    (PI.ScRefExists.WF.wFrame_of PI.ScRefExists.ApP.principal_ideal_ring_at_prime PI.ScRefExists.WB.weil_basis_existence)
