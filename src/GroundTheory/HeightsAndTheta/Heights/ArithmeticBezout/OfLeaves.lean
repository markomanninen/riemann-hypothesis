module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.RenameProdMapMul
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMean
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogGaussNormSupportFinite
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerMul
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.HeightMul
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRecursion
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PCharacterised

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem SphereMeanLinear.full : SphereMeanLinear.Statement := sphereMeanLinear

theorem ChowHeightMul.full : ChowHeightMul.Statement := chowHeightMul_of_mahlerMul mahlerMul

theorem ChowHeightRecursion.of_leaves (hV : ChowFormSectionVertical.Statement)
    (hA : MahlerSection.Statement) (hB : ChowFormBaseChange.Statement)
    (hAv : BaseChangeAvoid.Statement) : ChowHeightRecursion.Statement :=
  ChowHeightRecursion.proof hV hA hB hAv

end GroundTheory.Heights₂.Heights
