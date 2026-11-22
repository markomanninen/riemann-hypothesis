module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Af.satake_k_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.SatK := by
  intro P K _ _ _ n M π hπ w hw
  obtain ⟨⟨σ, hσ⟩, h⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P K n π w
  exact sat_of_isotypic (_root_.UpperTheory.V.Af.satake_local_of_printed_results P) π.finPart hπ w hw σ (h σ hσ)
end
