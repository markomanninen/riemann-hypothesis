module

public import Formalism.PeriodIntegrals.OrbRestr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetRestriction.OrbitRestriction

@[expose] public section

theorem PI.OrbRestr : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitRestriction E :=
  PI.OrbJet.OrbW.orbitRestriction
