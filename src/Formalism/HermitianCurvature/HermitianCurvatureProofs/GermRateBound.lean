module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateTopBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateLowerBound

@[expose] public section

theorem Formalism.FourierDecayAlt.P.germ_rate_bound : Formalism.FourierDecayAlt.P.GermFibreKernels.GermRateB :=
  Formalism.FourierDecayAlt.P.germ_rate_bound_of_split Formalism.FourierDecayAlt.P.germ_rate_lower_bound Formalism.FourierDecayAlt.P.germ_rate_top_bound
