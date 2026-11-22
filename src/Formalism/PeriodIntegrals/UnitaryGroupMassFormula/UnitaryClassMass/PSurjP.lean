module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjA

@[expose] public section

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem linOf_one_symm_apply {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (v : V) : (linOf b (1 : GL (Fin M) E)).symm v = v := by
  rw [LinearEquiv.symm_apply_eq, linOf_one_apply]

end PI.UnitaryGroupMassFormula.UJClassMass

end
