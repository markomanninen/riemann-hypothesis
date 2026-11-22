module

public import Formalism.PeriodIntegrals.HasseJidPow
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseJacobsonPowers.SfrMulMemJHfr
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HassePresH

@[expose] public section

theorem hasse_jid_power : PI.HasseJidPow := PI.HJP.hasseJidPow_of hasse_presentation
