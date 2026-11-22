module

public import Formalism.GaussJetBounds.GaussJetProofs.OneGauss
public import Formalism.GaussJetBounds.GaussJetProofs.CoefficientBoundMembership
public import Formalism.GaussJetBounds.StatementS
public import Formalism.GaussJetBounds.ThmAGauss

@[expose] public section

namespace Formalism.DworkPowerSeriesWeights

theorem oneLetterGauss : OneLetterGauss := one_letter_gauss_sum

end Formalism.DworkPowerSeriesWeights
