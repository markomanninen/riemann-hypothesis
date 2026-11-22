module

public import Formalism.PeriodIntegrals.LocHerm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.LocGlueOf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocOProj

@[expose] public section

theorem local_hermitian_glue : PI.LocHerm.LocGlue :=
  PI.LocHerm.Glue.locGlue_of projectiveOverOrder
