module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutDivisor
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutSpecialize
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutChart
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutChartSection
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutPreimage

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

theorem SegreFlagCutDivisor.closed : SegreFlagCutDivisor.Statement :=
  SegreFlagCutDivisor.proof SegreFlagCutSpecialize.proof
    (SegreFlagCutChart.proof SegreFlagCutChartSection.proof SegreFlagCutPreimage.proof)

end GroundTheory.Heights₂.Heights.NumbersDVR
