module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionNormSqExtension
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviLogFlat
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviHolPerturb
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviCompHol
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviFSInvariant

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem SectionNormSqExtension.closed : SectionNormSqExtension.Statement :=
  SectionNormSqExtension.proof LeviLogFlat.proof LeviHolPerturb.proof LeviCompHol.proof LeviFSInvariant.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
