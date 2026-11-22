module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeBaseComap
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KerAevalRatiosLe
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MIdealOverOneBlockEq
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemChartRingBlockVecIff
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BlockDegLeTotalDegree
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAlt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBis
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ProdNotMemPrimeOfForall
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisTer
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTail
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SpanSecsMemLocInSelf
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MConeMapOverOfIsMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RatioMonHomog
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ResidOfMem
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MIdealOverOneHeightslock
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRest
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurther
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNefBCut
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLast
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistModNatMul
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OfPowRealises
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSubEqChartSecOver
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PChartSecGen
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemChartOfMemSecOver
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtra
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistMulTwistTwistSys
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsAmpleBaseLocalizationEq
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockComp
public import Development.WeilBound.CoreStatements.HodgeTatePoints.A12

@[expose] public section

namespace PositivityTheory.HtPt.Ktw

theorem a21 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelCurves.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelCurves.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelCurvesDim.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelCurvesLift.proof

theorem a22 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BlockGenTransfer.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BlockGenTransfer.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ChartKernel.proof

theorem a23 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelPoint.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelPoint.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.BlockGenOfModel.proof a22
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelOfBlockGen.proof

theorem a24 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RealiseRestrict.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RealiseRestrict.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelGenerated.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SpanSecs.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ResidueMap.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ResidueGen.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RestrictGen.proof

theorem a25 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CurveNumModel.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CurveNumModel.proof a23 a24 a5 a18 a21

theorem a26 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelCurveNum.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelCurveNum.proof a25

theorem a27 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelChangeNef.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelChangeNef.proof a21 a26

theorem a28 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SegreRealise.Statement :=
  GroundTheory.Heights₂.Heights.ForSecondHalf.KleimanNefB.segreRealise a20 a27 a18

theorem a65 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelNefEq.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelNefEq.proof a20 a27

theorem a66 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.PowRealises.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.PowRealises.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelGenerated.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SpanSecs.proof

theorem a67 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelMulSecs.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelMulSecs.of_powRealises a66

theorem a68 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelTwistGenerated.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelTwistGenerated.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ChartSecGen.full

theorem a69 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelChangeGen.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelChangeGen.proof a68

theorem a70 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelChangeVeryAmple.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelChangeVeryAmple.proof a69

theorem a71 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelVeryAmpleEq.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelVeryAmpleEq.proof
    PositivityTheory.HtPt.KtwS.SectionsOverLocalization.VeryAmpleEq.full a67 a70

theorem a74 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.VeryAmpleModel.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.VeryAmpleModel.proof
    PositivityTheory.HtPt.KtwS.SectionsOverLocalization.VeryAmpleEq.full a69

end PositivityTheory.HtPt.Ktw
