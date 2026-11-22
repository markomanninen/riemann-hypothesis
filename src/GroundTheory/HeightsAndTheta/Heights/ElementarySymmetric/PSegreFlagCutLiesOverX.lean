module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutLiesOver
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutChartSection

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

theorem SegreFlagCutLiesOver.closed : SegreFlagCutLiesOver.Statement :=
  SegreFlagCutLiesOver.proof SegreFlagCutChartSection.proof

end GroundTheory.Heights₂.Heights.NumbersDVR
