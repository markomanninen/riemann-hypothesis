module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMixedDiffLinear
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDegLTClosure
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDiffStepExpansion
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDegLTOfUnitSteps
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDegLTEventuallyConst
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PEventualValueFacts
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbFnVanishBlock
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGradedPieceQuot
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutPieces
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbFnCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultiHomogPrimeCriterion
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PColonMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PAssociatedMultiHomogPrime
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFiltrationStepHilb
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFiltrationStepLength
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPrimeFiltration
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultAtPrimeAtMinimal
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimStrictDrop
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlockAdjoinPrime
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRelevantDimGe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbDegBound
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTopDimMinimal
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumOfFiltration
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumAssoc
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByForm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGradedPieceFree
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialPieceRank
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericPieceRank
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealCorresp
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealSurj
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialMultAt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialCycleEval
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialDimBound
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConservationOfNumber
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumVanish
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem MixedDiffLinear.full : MixedDiffLinear.Statement := MixedDiffLinear.proof

theorem DegLTClosure.full : DegLTClosure.Statement := DegLTClosure.proof MixedDiffLinear.full

theorem DiffStepExpansion.full : DiffStepExpansion.Statement := DiffStepExpansion.proof

theorem DegLTOfUnitSteps.full : DegLTOfUnitSteps.Statement :=
  DegLTOfUnitSteps.proof DiffStepExpansion.full MixedDiffLinear.full DegLTClosure.full

theorem DegLTEventuallyConst.full : DegLTEventuallyConst.Statement :=
  DegLTEventuallyConst.proof MixedDiffLinear.full

theorem EventualValueFacts.full : EventualValueFacts.Statement := EventualValueFacts.proof

theorem HilbFnVanishBlock.full : HilbFnVanishBlock.Statement.{u} := HilbFnVanishBlock.proof

theorem GradedPieceQuot.full : GradedPieceQuot.Statement.{u} := GradedPieceQuot.proof

theorem CutPieces.full : CutPieces.Statement.{u} := CutPieces.proof

theorem HilbFnCut.full : HilbFnCut.Statement.{u} := HilbFnCut.proof GradedPieceQuot.full CutPieces.full

theorem MultiHomogPrimeCriterion.full : MultiHomogPrimeCriterion.Statement.{u} :=
  MultiHomogPrimeCriterion.proof

theorem ColonMultiHomog.full : ColonMultiHomog.Statement.{u} := ColonMultiHomog.proof

theorem AssociatedMultiHomogPrime.full : AssociatedMultiHomogPrime.Statement.{u} :=
  AssociatedMultiHomogPrime.proof MultiHomogPrimeCriterion.full ColonMultiHomog.full

theorem FiltrationStepHilb.full : FiltrationStepHilb.Statement.{u} := FiltrationStepHilb.proof

theorem FiltrationStepLength.full : FiltrationStepLength.Statement.{u} := FiltrationStepLength.proof

theorem PrimeFiltration.full : PrimeFiltration.Statement.{u} :=
  PrimeFiltration.proof AssociatedMultiHomogPrime.full FiltrationStepHilb.full
    FiltrationStepLength.full ColonMultiHomog.full

theorem MultAtPrimeAtMinimal.full : MultAtPrimeAtMinimal.Statement.{u} := MultAtPrimeAtMinimal.proof

theorem DimStrictDrop.full : DimStrictDrop.Statement.{u} := DimStrictDrop.proof

theorem BlockAdjoinPrime.full : BlockAdjoinPrime.Statement.{u} := BlockAdjoinPrime.proof

theorem RelevantDimGe.full : RelevantDimGe.Statement.{u} := RelevantDimGe.proof BlockAdjoinPrime.full

theorem HilbDegBound.full : HilbDegBound.Statement.{u} :=
  HilbDegBound.proof HilbFnVanishBlock.full HilbFnCut.full PrimeFiltration.full DimStrictDrop.full
    RelevantDimGe.full DegLTClosure.full DegLTOfUnitSteps.full

theorem TopDimMinimal.full : TopDimMinimal.Statement.{u} := TopDimMinimal.proof DimStrictDrop.full

theorem IntNumOfFiltration.full : IntNumOfFiltration.Statement.{u} :=
  IntNumOfFiltration.proof MixedDiffLinear.full DegLTEventuallyConst.full EventualValueFacts.full

theorem GradedPieceFree.full : GradedPieceFree.Statement.{u} := GradedPieceFree.proof

theorem SpecialPieceRank.full : SpecialPieceRank.Statement.{u} :=
  SpecialPieceRank.proof GradedPieceFree.full

theorem GenericPieceRank.full : GenericPieceRank.Statement.{u} := GenericPieceRank.proof

theorem SpecialIdealMultiHomog.full : SpecialIdealMultiHomog.Statement.{u} :=
  SpecialIdealMultiHomog.proof

theorem SpecialIdealCorresp.full : SpecialIdealCorresp.Statement.{u} := SpecialIdealCorresp.proof

theorem SpecialIdealSurj.full : SpecialIdealSurj.Statement.{u} := SpecialIdealSurj.proof

theorem SpecialMultAt.full : SpecialMultAt.Statement.{u} := SpecialMultAt.proof

theorem SpecialCycleEval.full : SpecialCycleEval.Statement.{u} :=
  SpecialCycleEval.proof SpecialIdealCorresp.full SpecialIdealSurj.full SpecialMultAt.full

theorem SpecialDimBound.full : SpecialDimBound.Statement.{u} := SpecialDimBound.proof

theorem IntNumVanish.full : IntNumVanish.Statement.{u} :=
  IntNumVanish.proof HilbDegBound.full HilbFnVanishBlock.full DegLTClosure.full EventualValueFacts.full

theorem IntNumAssoc.full : IntNumAssoc.Statement.{u} :=
  IntNumAssoc.proof PrimeFiltration.full IntNumOfFiltration.full MultAtPrimeAtMinimal.full
    IntNumVanish.full TopDimMinimal.full HilbDegBound.full

theorem CutByForm.full : CutByForm.Statement.{u} :=
  CutByForm.proof IntNumAssoc.full HilbFnCut.full MixedDiffLinear.full

theorem ConservationOfNumber.full : ConservationOfNumber.Statement.{u} :=
  ConservationOfNumber.proof IntNumAssoc.full SpecialCycleEval.full SpecialPieceRank.full
    GenericPieceRank.full SpecialIdealMultiHomog.full SpecialDimBound.full

end GroundTheory.Heights₂.Heights.NumbersDVR
