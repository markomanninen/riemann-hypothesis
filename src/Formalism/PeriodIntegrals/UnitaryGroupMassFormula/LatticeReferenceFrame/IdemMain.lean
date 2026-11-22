module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.IdemLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.IdemAd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.IdemTen

@[expose] public section

namespace PI.ScRefExists.Id

theorem idemLift : PI.ScRefExists.Sk.IdemLift :=
  idemLift_of_steps locIdem adOfLoc fixInt tenStep

end PI.ScRefExists.Id
