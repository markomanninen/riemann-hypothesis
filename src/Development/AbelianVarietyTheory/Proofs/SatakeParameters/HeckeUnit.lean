module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT

@[expose] public section

open GlobalTheory.ColPeriod

namespace GlobalTheory.ColPeriod

theorem heckeUnit : GlobalTheory.ColPeriod.HeckeUnit :=
  fun _ _ _ _ _ _ _ _ hX hPr hμ _ _ _ _ hw hP x _ hk => GlobalTheory.CharVal.mu_unit hX hPr hμ x hk hP hw

end GlobalTheory.ColPeriod
