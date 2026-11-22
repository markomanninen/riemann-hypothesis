module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BoundOnEarlierRegion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffFormOf

@[expose] public section

theorem Formalism.FourierDecayAlt.P.wave_difference_form : Formalism.FourierDecayAlt.P.PBO.WaveDiffForm :=
  Formalism.FourierDecayAlt.P.StandardPairingDecay.waveDiffForm_of Formalism.FourierDecayAlt.P.StandardPairingDecay.bound_on_earlier_region
