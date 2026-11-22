module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable

@[expose] public section

namespace GlobalTheory

theorem besselXiIntegrable_holds : GlobalTheory.HCXi.BesselXiIntegrable :=
  ReciprocityTheory.ChartRestriction.DS.Xi.xiExists

end GlobalTheory
