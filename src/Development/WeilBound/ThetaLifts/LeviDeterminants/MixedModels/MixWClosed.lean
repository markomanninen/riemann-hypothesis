module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.MixWOfAdel
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdelicEstimatesHolds

@[expose] public section

theorem PositivityTheory.Mix.mixW_closed : PositivityTheory.ThKG.MixW := PositivityTheory.ThKF0.mixW_of_adel PositivityTheory.Mix.adelic_estimates_holds
