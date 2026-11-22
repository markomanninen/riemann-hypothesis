module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHSFull
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelSectionsLarge
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelChartPoly
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelOneStep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelTorsionBound

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

theorem RelSectionsLarge.full : RelSectionsLarge.Statement :=
  RelSectionsLarge.proof RelChartPoly.proof (RelOneStep.proof RelChartPoly.proof RelTorsionBound.proof)

end GroundTheory.Heights₂.Heights.Targets
