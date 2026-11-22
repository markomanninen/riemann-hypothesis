module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomogIdeal
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabDivCycle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumPoint
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumRatSection
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumIsFieldIntersection
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBase
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumAdd
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRational

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem IntNumIsFieldIntersection.of_intNumBase_cutRational
    (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u}) :
    IntNumIsFieldIntersection.Statement.{u} :=
  IntNumIsFieldIntersection.proof VocabMultiHomog.proof
    (VocabMultiHomogIdeal.proof VocabMultiHomog.proof) VocabDivCycle.proof
    (IntNumPoint.proof hBase) (IntNumRatSection.proof hCut)

end GroundTheory.Heights₂.Heights.NumbersDVR
