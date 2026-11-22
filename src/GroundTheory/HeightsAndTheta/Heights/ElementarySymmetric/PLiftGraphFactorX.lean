module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphFactor
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSectionNormSqExtensionX

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

theorem LiftGraphFactor.closed : LiftGraphFactor.Statement :=
  LiftGraphFactor.proof GroundTheory.Heights₂.Heights.HilbertSamuel.SectionNormSqExtension.closed

end GroundTheory.Heights₂.Heights.Targets
