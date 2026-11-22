module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDAsm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDAdP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDSI
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDMatP
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxADAlg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxAJacE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxKLevi

@[expose] public section

namespace PI.UnitaryDimensionFormula

theorem idxSurj_of_frame (hFr : IdxDFrame) : IdxSurj :=
  idxSurj_of idxDAlg idxDAd idxDInt idxDSig hFr (idxDMat_of idxDJacE) idxDLevi

end PI.UnitaryDimensionFormula
