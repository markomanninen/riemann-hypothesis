module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.IntSOfSIntFin
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.InHolds
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.JSIntFin

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.NVHTop

theorem intS : S0.IntSStatement :=
  S0.IntS.intS_of_sIntFin (Mult1.S0.sIntFin Mult1.multiplicity_one_hypotheses_hold)

end ReciprocityTheory.ChartRestriction.DS.Lap.NVHTop
