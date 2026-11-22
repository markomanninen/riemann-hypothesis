module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.GlueHoldsVar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.HighGOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.ChainSt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.InvOmega
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.FirstJetIntegralGeneralHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.SecondJetIntegralGeneralHolds

@[expose] public section

theorem jets_high_generation : PI.JetsPhW.HighG :=
  PI.JetsPhW.W.highG_of PI.JetsPhW.W.derivative_chain_rule PI.JetsPhW.W.derivative_self
    PI.JetsPhW.W.pderiv_subst_ne PI.JetsPhW.W.pderiv_subst_self PI.JetsPhW.W.evaluation_at_zero
    PI.JetsPhW.W.jet_derivative_integrality PI.JetsPhW.W.log_derivative_integral_jet_integrality PI.JetsPhW.W.derivative_integral

theorem jets_phase_weights : PI.JetsPhW.Target :=
  PI.JetsPhW.W.glue_holds_var PI.JetsPhW.Inv.inverse_omega_holds jets_high_generation
    PI.JetsPhW.Low.firstJetIntegralGeneral_holds PI.JetsPhW.Low.secondJetIntegralGeneral_holds

theorem jets_high : PI.JetsPhW.High :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).1

theorem jets_one : PI.JetsPhW.One :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).2.1

theorem jets_two : PI.JetsPhW.Two :=
  (show PI.JetsPhW.High ∧ PI.JetsPhW.One ∧ PI.JetsPhW.Two from jets_phase_weights).2.2
