module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleDim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensSpan
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpanBundleDim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPointIdealMultiProj
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpanBundleTrdegGe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpanBundleTrdegLe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionForms
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionDiv
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultAtOfSaturated
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PProjIdealFormValue
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTruncSpecialize
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleChartSection
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineSection
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineDegree
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeLocalFlat
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeLocalLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConePolyLocalization
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarInj
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarNumerator
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarSurj
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarUnit
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocalRing
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocDim
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocFrac
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocLocalize
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocLocal
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocNoetherian
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocResidue
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocSeparate
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocUnits
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleMinimal
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreFinite
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreNonempty
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreRelDim
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFiniteAlgebraLengthSum
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFunctionFieldFinite
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PLocalIntegralClosureFinite
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PLocalizedQuotientLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartDehomog
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartHomog
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartLocDim
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartTrdeg
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PNoetherIntegralClosure
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFinite
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFiniteRank
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalIntegral
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLengthSum
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalMaxIdeals
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalResidueLength
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PValuativeCentre
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForwardLocal

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR


open GroundTheory.Heights₂.Heights.FieldNumbers in
theorem DivPushForwardLocalZero : FieldNumbers.DivPushForwardLocal.Statement.{0} := by
  have hq := DegZeroLocQuot.proof.{0}
  have hdzl := DegZeroLocLocal.proof hq
  have hdzn := DegZeroLocNoetherian.proof hq
  have hmh := MChartHomog.proof.{0}
  have hmd := MChartDehomog.proof.{0}
  have hmt := MChartTrdeg.proof hmh
  have hdzr := DegZeroLocalRing.proof hdzl hdzn
    (DegZeroLocDim.proof hmh hmt (MChartLocDim.proof hq hmd hmh))
  have hnum := ConeVarNumerator.proof hq
  have hcone := ConeLocalLength.proof LocalizedQuotientLength.proof
    (ConeLocalFlat.proof (ConePolyLocalization.proof hdzl (ConeVarUnit.proof hq hnum)
      ConeVarSurj.proof (ConeVarInj.proof hnum)))
  have hfr := DegZeroLocFrac.proof.{0}
  have hff := FibreFinite.proof.{0}
  have hint := SemilocalIntegral.proof ValuativeCentre.proof.{0}
  have hrank := SemilocalFiniteRank.proof hff
    (SemilocalFinite.proof hint
      (LocalIntegralClosureFinite.proof NoetherIntegralClosureFinite.proof
        (FunctionFieldFinite.proof hmd hmt) hq hmd hfr) hdzn) hfr
  have hfrd := FibreRelDim.proof.{0}
  have hlz := DegZeroLocLocalize.proof.{0}
  have hres := DegZeroLocResidue.proof.{0}
  have hmaxi := SemilocalMaxIdeals.proof hff hfrd (FibreNonempty.proof hrank hdzr)
    DegZeroLocUnits.proof DegZeroLocSeparate.proof hlz (SemilocalResidueLength.proof hres hrank hlz)
  have hlen := SemilocalLength.proof
    (SemilocalLengthSum.proof hff hrank hdzr FiniteAlgebraLengthSum.proof hmaxi) hfrd
    DivCycleMinimal.proof hcone
  exact DivPushForwardLocal.proof DivCycleMinimal.proof hcone hdzr hrank hlen

theorem FlagBundleDim.full : FlagBundleDim.Statement :=
  FlagBundleDim.proof TwistedDualGensSpan.proof
    (SpanBundleDim.proof PointIdealMultiProj.proof SpanBundleTrdegGe.proof SpanBundleTrdegLe.proof)

theorem NumericalSegre.full : NumericalSegre.Statement :=
  NumericalSegre.of_open FlagBundleDim.full FlagBundleSectionForms.proof
    (FlagBundleSectionDiv.proof FlagBundleDim.full MultAtOfSaturated.proof ProjIdealFormValue.proof
      TruncSpecialize.proof FlagBundleChartSection.proof)
    FlagLineSection.proof FlagLineDegree.proof DivPushForwardLocalZero

end GroundTheory.Heights₂.Heights.NumbersDVR
