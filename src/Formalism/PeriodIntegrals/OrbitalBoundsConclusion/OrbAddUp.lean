module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.ConstantCoeffZeroOfBoundGeneral

@[expose] public section

theorem PI.OrbAddUp : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitsAddLowerBound E :=
  PI.OrbJet.AU.orbAddUp_main
