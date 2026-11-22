module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitAlt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagModelRootIndep
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelValueIndependentStatement

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.RootIndep

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelRootIndependence.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelRootIndependence.proof GlobalTheory.T.flag_model_value_independent

end GlobalTheory.CompanionTheory.Ar.RootIndep
