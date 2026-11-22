module

public import Formalism.HermitianCurvature.StatementB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem exists_auxiliary_xi : Formalism.FourierDecayAlt.B.XiExists := ReciprocityTheory.ChartRestriction.DS.Xi.xiExists

end Formalism.FourierDecayAlt.P
