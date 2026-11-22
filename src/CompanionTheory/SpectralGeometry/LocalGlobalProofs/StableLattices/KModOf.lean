module

public import Mathlib
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional

@[expose] public section

namespace GlobalTheory.CompanionTheory.KModOfStep

theorem kModOf : CompanionTheory.RgExh.Fin.KModOf := by
  intro n ε H _ _ _ σ hU hI
  exact CompanionTheory.D.LK.hKModExists n ε H σ hU hI

end GlobalTheory.CompanionTheory.KModOfStep
