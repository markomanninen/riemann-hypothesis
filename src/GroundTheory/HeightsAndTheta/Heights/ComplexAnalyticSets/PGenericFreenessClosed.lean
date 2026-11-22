module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericFreeness
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericNoetherNormalisation

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v w

theorem GenericFreeness.full : GenericFreeness.Statement.{u, v, w} :=
  GenericFreeness.proof GenericNoetherNormalisation.proof

end GroundTheory.Heights₂.Heights
