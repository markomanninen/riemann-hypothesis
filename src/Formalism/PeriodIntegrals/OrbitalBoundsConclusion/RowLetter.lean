module

public import Mathlib
public import Formalism.PeriodIntegrals.RowLetter
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.ChainRule
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.NvFalseEq

@[expose] public section

theorem row_letter_rule : PI.RowLetter :=
  PI.RL.W.rowLetter_of PI.RL.W.chainRule PI.RL.W.vecX PI.RL.W.keyCov PI.RL.W.hdHom
