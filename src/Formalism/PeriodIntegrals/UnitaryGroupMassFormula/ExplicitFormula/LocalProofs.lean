module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LocalAbstract

@[expose] public section

namespace PI.EF

theorem localAbstract_of (hDF : PI.DiscFactor) (hDL : PI.DiscLog) : LocalAbstract := by
  intro r R' R hr hrR' hR'R
  exact ⟨Loc.locC r R' R, Loc.locC_pos hr hrR' hR'R, fun f s₀ M hf hf0 hM hb =>
    Loc.local_abstract hDF hDL hr hrR' hR'R f s₀ M hf hf0 hM hb⟩

end PI.EF
