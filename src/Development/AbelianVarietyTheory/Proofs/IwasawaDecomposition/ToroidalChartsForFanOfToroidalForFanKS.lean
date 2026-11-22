module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

@[expose] public section

namespace GlobalTheory

theorem toroidalChartsForFan_of_toroidalForFanKS :
    GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.ToroidalChartsForFan :=
  fun h => h.toroidalChartsForFan

end GlobalTheory
