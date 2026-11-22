module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefLoc

@[expose] public section

namespace GlobalTheory.Sloc.CoefWeighted

theorem coefWeightedLoc_uncond : Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc :=
  ReciprocityTheory.ChartRestriction.DS.coefWeightedLoc

end GlobalTheory.Sloc.CoefWeighted
