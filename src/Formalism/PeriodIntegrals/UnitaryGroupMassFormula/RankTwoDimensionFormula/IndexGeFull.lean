module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IndexGe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxAUni
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxKHom
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDChk
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDcvFrameAsm

@[expose] public section

namespace PI.UnitaryDimensionFormula

theorem indexGe : IndexGe := indexGe_of uniSub idxHom (idxSurj_of_frame idxDFrame)

end PI.UnitaryDimensionFormula
