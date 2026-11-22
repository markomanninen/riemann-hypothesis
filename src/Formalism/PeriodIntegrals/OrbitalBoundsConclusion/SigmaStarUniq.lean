module

public import Mathlib
public import Formalism.PeriodIntegrals.SigmaStarUniq
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AreaLat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.SigmaStarUniqOf

@[expose] public section

theorem sigma_star_unique : PI.SigmaStarUniq := PI.SSU.sigmaStarUniq_of area_lattice_formula
