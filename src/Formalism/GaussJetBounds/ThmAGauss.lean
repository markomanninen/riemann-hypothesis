module

public import Formalism.GaussJetBounds.GaussJetProofs.ThmAGaussOf
public import Formalism.GaussJetBounds.GaussJetProofs.Transfer
public import Formalism.GaussJetBounds.GaussJetProofs.FJEval
public import Formalism.GaussJetBounds.GaussJetProofs.Labels

@[expose] public section

namespace Formalism.DworkPowerSeriesWeights

theorem thmAGauss : ThmAGauss :=
  thmAGauss_of admissibleTransfer frame_jet_evaluation labelsExist_statement gauss_sum_powers

end Formalism.DworkPowerSeriesWeights
