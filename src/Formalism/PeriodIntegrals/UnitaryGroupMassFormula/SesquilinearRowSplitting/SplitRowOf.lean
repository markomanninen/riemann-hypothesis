module

public import Mathlib
public import Formalism.PeriodIntegrals.SplitRow
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoreStep

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.SRW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem splitRow_of (hc : CoreStep) (ha : AaStep) (ht : TrStep) : PI.SplitRow.SplitRow := by
  intro D u F0 Λ hΛ
  obtain ⟨hg, hF, hX⟩ := hΛ
  exact hc _ _ _ _ _ F0 Λ ⟨hg.1.toIsLattice, hF.2.1, hF.2.2.1.1, hF.2.2.2.2,
    hX.trans (Formalism.L2.SG.Saturated.latSpan_aaS D F0).symm,
    fun a => (ha D a).1, fun a => (ha D a).2, ht D⟩

end PI.SRW
