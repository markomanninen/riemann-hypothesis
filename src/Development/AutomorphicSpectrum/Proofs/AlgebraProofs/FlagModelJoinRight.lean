module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSubAlt
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSJoinright
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairNumberPullbackStatement

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinRightAlt.Statement :=
  PositivityTheory.Xgn.A_s_joinright.of_pullback GlobalTheory.T.pair_number_pullback

end GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight
