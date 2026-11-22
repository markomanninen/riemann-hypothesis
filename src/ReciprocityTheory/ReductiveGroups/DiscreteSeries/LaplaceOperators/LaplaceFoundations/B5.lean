module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.LieExponentialMajorantHolds

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

theorem b5 : CayleyMajorantBound := LieExponentialMajorant.lieExponentialMajorant_holds

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
