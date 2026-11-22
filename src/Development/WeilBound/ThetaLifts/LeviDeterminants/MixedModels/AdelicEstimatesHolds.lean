module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MCGlue
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MCReal
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.TraceNondeg
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MCPure
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.FiniteAdelicEstimatesHolds

@[expose] public section

theorem PositivityTheory.Mix.adelic_estimates_holds : PositivityTheory.Mix.AdelSt :=
  PositivityTheory.Mix.adelSt_of PositivityTheory.Mix.pure_tensor_estimates_holds PositivityTheory.Mix.finite_adelic_estimates_holds (PositivityTheory.Mix.infSt_of PositivityTheory.Mix.real_estimates_holds)
