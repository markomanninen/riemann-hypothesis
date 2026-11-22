module

public import Formalism.GaussJetBounds.GaussJetProofs.LemmaRA
public import Formalism.GaussJetBounds.GaussJetProofs.TheoremAOneMonomialLogLoss
public import Formalism.GaussJetBounds.GaussJetProofs.MinorProductSupportTop

@[expose] public section

universe u v

namespace Formalism.DworkPowerSeriesWeights

theorem thmAJetA : ThmAJetA.{u} := theorem_A_one_monomial_log_loss

end Formalism.DworkPowerSeriesWeights
