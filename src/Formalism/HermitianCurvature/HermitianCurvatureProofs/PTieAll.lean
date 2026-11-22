module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtieLevTransportHerOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SfiniteOfHaar

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem ptie_levTransportHer_of_sliceStep (hS : Formalism.FourierDecayAlt.P.PTie.SliceStepHer) : Formalism.FourierDecayAlt.P.PTie.LevTransportHer :=
  ptie_levTransportHer_of jacquet_scaling hS

end Formalism.FourierDecayAlt.P
