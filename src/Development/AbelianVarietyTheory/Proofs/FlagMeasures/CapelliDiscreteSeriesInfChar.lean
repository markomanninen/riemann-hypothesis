module

public import Mathlib
public import Formalism.PeriodIntegrals.DSInfCharCap
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter

@[expose] public section

namespace GlobalTheory

theorem capelliDiscreteSeriesInfChar : PI.DSInfCharCap.DSInfCharCap :=
  CompanionTheory.D.DSIC.discrete_series_infinitesimal_character

end GlobalTheory
