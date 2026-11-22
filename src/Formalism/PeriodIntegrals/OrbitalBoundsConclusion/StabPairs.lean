module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.Assembly
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.ConverseStepOf

@[expose] public section

theorem stabPairs : Formalism.FourierDecayAlt.C2.CurvatureConditionOneClauseThree :=
  PI.StabPairsW.stabPairs_of_converse (PI.StabPairs.Conv.converseStep_of PI.StabPairsW.gram_matrix_invariance)
