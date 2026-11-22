module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PVectorOrbitsFinite
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerExtra

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

theorem LineIndexNeZero.proof (E W : Type*) [Field E] [NumberField E] [AddCommGroup W]
    [Module E W] : LineIndexNeZero.Statement E W :=
  _root_.UpperTheory.Reformulated.B.Gub1.proof E W

end GroundTheory.Heights₂.Heights.FiniteCovolume
