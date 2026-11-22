module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.LocSplitChiOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertQRG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CommensuratedOfIsOpenIsCompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CompactLocalGlobal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.LiftMatMapSame
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Reduce

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

theorem indexEq_of_open (hG : GLChi) (hQ : QReflPow) : PI.AdIndexEq.IndexEq :=
  indexEq_of_loc compact_commensurated lift_unitary' matrix_v_injective matrix_v_unitary compact_local_global reduce_local
    (locSplitChi_of hG) (locInertChi_of_qReflPow hQ)

end PI.UnitaryGroupMassFormula.AdIndexEq

end
