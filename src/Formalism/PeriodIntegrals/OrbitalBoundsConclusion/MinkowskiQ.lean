module

public import Mathlib
public import Formalism.PeriodIntegrals.MinkowskiQ
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Minkowski
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiTorsionFree.Lattice

@[expose] public section

theorem minkowski_bound_rat : PI.MinkowskiBoundQ := PI.MkQ.minkowskiBoundQ
