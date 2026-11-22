module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PNumericalSegre
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundlePullbackVanish
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSymmetricSpanHsymm
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairCocycle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSubQuotient
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMore
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.WithBotLtNatCastOfAddOneLe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IdealCycleSupportFinite
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVNumCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVertCutEff
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivisorIdealCycle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Imports
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivCycleEqZeroOfFormNotMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RelevantMinimalOfDivCycleNeZero
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExistsMultiHomogNotMemOfIsRelevant
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExceptionalDeg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBis
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CycEvalAddOfFinite
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RatDiv
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.WithBotLtOfAddOneLe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LtNatCastOfAddOneLe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleLineBase
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHsymmPairFlagIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTer
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CycEvalCongrOnSupport
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForward
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem SymmetricSpanHsymm.full : SymmetricSpanHsymm.Statement := SymmetricSpanHsymm.proof

theorem DivisorIdealCycle.full : DivisorIdealCycle.Statement.{u} := DivisorIdealCycle.proof

theorem VNumCut.full : VNumCut.Statement.{u} := VNumCut.proof CutByForm.full

theorem VertCutEff.full : VertCutEff.Statement.{u} :=
  VertCutEff.proof VNumCut.full DivisorIdealCycle.full IntNumAddFirst.full

theorem LeftExpansion.full : LeftExpansion.Statement.{u} := LeftExpansion.proof VNumCut.full

theorem RightExpansion.full : RightExpansion.Statement.{u} :=
  RightExpansion.proof VertCutEff.full DivisorIdealCycle.full

theorem ExcessPositive.full : ExcessPositive.Statement.{u} := ExcessPositive.proof

theorem AvoidingFormExists.full : AvoidingFormExists.Statement.{u} := AvoidingFormExists.proof

theorem HorizontalAvoidingForm.full : HorizontalAvoidingForm.Statement.{u} :=
  HorizontalAvoidingForm.proof

theorem LeftSideAdditiveInDegree.full : LeftSideAdditiveInDegree.Statement.{u} := LeftSideAdditiveInDegree.proof

theorem RightSideMultiplicativeInForm.full : RightSideMultiplicativeInForm.Statement.{u} :=
  RightSideMultiplicativeInForm.proof DivCycleMul.full DivCycleFiniteSupport.full

theorem CommonFactorRemoval.full : CommonFactorRemoval.Statement.{u} := CommonFactorRemoval.proof DivCycleMul.full

theorem AdditivityInDivisor.full : AdditivityInDivisor.Statement.{u} :=
  AdditivityInDivisor.proof DivCycleMul.full DivCycleFiniteSupport.full IntNumAddFirst.full
    SupSpanMultiHomog.full MinimalPrimeMultiHomog.full SpecialIdealMultiHomog.full
    SpecialIdealCorresp.full SpecialQuotDim.full DimStrictDrop.full

theorem TautologicalCase.full : TautologicalCase.Statement.{u} :=
  TautologicalCase.proof IntNumAddFirst.full MinimalPrimeMultiHomog.full SupSpanMultiHomog.full
    SpecialQuotDim.full SpecialIdealCorresp.full SpecialIdealMultiHomog.full DimStrictDrop.full

theorem FlagBundlePullbackVanish.of_open (hdim : FlagBundleDim.Statement) :
    FlagBundlePullbackVanish.Statement :=
  FlagBundlePullbackVanish.proof FieldNumbers.ProjectionFormulaContracted.full hdim

theorem FlagBundleCut.of_open (hdim : FlagBundleDim.Statement)
    (hforms : FlagBundleSectionForms.Statement) (hdiv : FlagBundleSectionDiv.Statement) :
    FlagBundleCut.Statement :=
  FlagBundleCut.proof hdim hforms hdiv FieldNumbers.CutRational.full

theorem FlagBundleLineBase.of_open (hdim : FlagBundleDim.Statement)
    (hsec : FlagLineSection.Statement) (hdeg : FlagLineDegree.Statement)
    (hloc : FieldNumbers.DivPushForwardLocal.Statement.{0}) : FlagBundleLineBase.Statement :=
  FlagBundleLineBase.proof hdim hsec hdeg
    (FieldNumbers.ProjectionFormulaDegree.of_divPushForward
      (FieldNumbers.DivPushForward.proof FieldNumbers.ContractRelDimLe.proof hloc))

theorem NumericalSegre.of_open (hdim : FlagBundleDim.Statement)
    (hforms : FlagBundleSectionForms.Statement) (hdiv : FlagBundleSectionDiv.Statement)
    (hsec : FlagLineSection.Statement) (hdeg : FlagLineDegree.Statement)
    (hloc : FieldNumbers.DivPushForwardLocal.Statement.{0}) : NumericalSegre.Statement :=
  NumericalSegre.proof FieldNumbers.IntNumAdd.full hdim (FlagBundleCut.of_open hdim hforms hdiv)
    (FlagBundlePullbackVanish.of_open hdim) (FlagBundleLineBase.of_open hdim hsec hdeg hloc)

theorem LocalCoefficient.of_open (hl : LeftTermSupport.Statement.{u})
    (hr : RightTermSupport.Statement.{u}) (hring : LocalCoeffRing.Statement.{u}) :
    LocalCoefficient.Statement.{u} :=
  LocalCoefficient.proof hl hr hring

theorem NoCommonComponentCase.of_open (hl : LeftTermSupport.Statement.{u})
    (hr : RightTermSupport.Statement.{u}) (hring : LocalCoeffRing.Statement.{u}) :
    NoCommonComponentCase.Statement.{u} :=
  NoCommonComponentCase.proof LeftExpansion.full RightExpansion.full (LocalCoefficient.of_open hl hr hring)
    IntNumVanish.full

theorem BlowUpModel.of_open (hrees : ReesAlgebraDim.Statement.{u}) : BlowUpModel.Statement.{u} :=
  BlowUpModel.proof hrees

theorem BlowUpDecomposition.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) : BlowUpDecomposition.Statement.{u} :=
  BlowUpDecomposition.proof (BlowUpModel.of_open hrees) hst

theorem BlowUpInvariance.of_open (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) : BlowUpInvariance.Statement.{u} :=
  BlowUpInvariance.proof hvert hdiv hhor hcomp DivCycleFiniteSupport.full

theorem BlowUpReduction.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) : BlowUpReduction.Statement.{u} :=
  BlowUpReduction.proof (BlowUpDecomposition.of_open hrees hst)
    (BlowUpInvariance.of_open hvert hdiv hhor hcomp) CommonFactorRemoval.full AdditivityInDivisor.full
    RightSideMultiplicativeInForm.full LeftSideAdditiveInDegree.full TautologicalCase.full

theorem CommonFactorInduction.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) (hdrop : BlowUpExcessDecreases.Statement.{u})
    (hvert : BlowUpVerticalPush.Statement.{u}) (hdiv : BlowUpDivisorPush.Statement.{u})
    (hhor : BlowUpHorizontalCorresp.Statement.{u}) (hcomp : HorizontalComponentModel.Statement.{u}) :
    CommonFactorInduction.Statement.{u} :=
  CommonFactorInduction.proof ExcessPositive.full AvoidingFormExists.full HorizontalAvoidingForm.full
    (BlowUpDecomposition.of_open hrees hst) hdrop
    (BlowUpReduction.of_open hrees hst hvert hdiv hhor hcomp) LeftSideAdditiveInDegree.full RightSideMultiplicativeInForm.full
    DivCycleMul.full

end GroundTheory.Heights₂.Heights.NumbersDVR
