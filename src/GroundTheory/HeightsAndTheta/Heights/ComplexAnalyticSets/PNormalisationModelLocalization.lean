module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalisationModelLocalization
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNormalisationModelLocalizationX

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem NormalisationModelLocalization.full : NormalisationModelLocalization.Statement :=
  NormalisationModelLocalization.proof

end GroundTheory.Heights₂.Heights
