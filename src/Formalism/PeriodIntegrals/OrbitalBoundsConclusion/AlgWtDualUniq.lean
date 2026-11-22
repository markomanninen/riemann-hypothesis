module

public import Mathlib
public import Formalism.LocalToGlobal.AdelicCompactOpens.UniROfUniRT
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightDualUniqueness.Imports

@[expose] public section

theorem algebraic_weight_dual_unique (L : Type) [Field L] [NumberField L] [NumberField.IsCMField L] (n : ℕ) : Formalism.L2.Props.DualUnique L n :=
  PI.UnitaryGroupMassFormula.AlgWtDualUniq.main L n
