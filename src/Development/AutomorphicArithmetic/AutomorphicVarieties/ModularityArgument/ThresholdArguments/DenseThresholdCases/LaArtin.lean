module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinConv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocLaArtinLit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Z.Win.T2.laArtinLit' :
    _root_.UpperTheory.V.Loc.localArtinReciprocity_type := by
  intro N F Ω _ _ _ _ _ A w h
  obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt N h
  obtain ⟨a, ha, ε, -⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  exact ⟨a, ha⟩
end
