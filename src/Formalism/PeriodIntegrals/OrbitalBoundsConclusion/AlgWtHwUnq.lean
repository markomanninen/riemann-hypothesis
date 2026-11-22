module

public import Formalism.PeriodIntegrals.AlgWtHwUnq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.DensityFirstBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GeneralLinearReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GlueStepSubstitution

@[expose] public section

theorem algebraic_weight_highest_unique (L : Type) [Field L] [NumberField L] [NumberField.IsCMField L] (n : ℕ) : PI.AlgWtHwUnq.Stmt L n :=
  fun a τ lam lam' h1 h2 =>
    PI.UnitaryGroupMassFormula.HwConjInf.glue_holds_var PI.UnitaryGroupMassFormula.HwConjInf.density_induction PI.UnitaryGroupMassFormula.HwConjInf.general_linear_reduction L n a τ lam lam' h1 h2
