module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RenameBaseHomogeneousComponent
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsFormDivOfMemChartRing
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsAlgebraicAdjoin
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ProdExp
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTail
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SpanSecsMemLocInSelf
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.FoldTensorToSubSystem
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCombCyclic
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCombContract
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHTheoremSFree
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeEmbed
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeDecomp
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeIndep
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHFreeBadFinite
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechSES
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechDSq
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechDDeg
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHTheoremS
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHPrimeFilt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperComponentMulX
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PEulerVarX
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsPolyBackDiffPow
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotPartEqGradedPiece
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsPowSmulEqZero
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisBis
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsFormOfMemChartRingOver
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellMeetsPt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsPowOfMemCellSec
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SetCApplyNotMem
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellDMulLeft
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiHomogRename
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRowLocCoverX
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellMeetsBaseCell
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SgnSingleton
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDoubleCechX
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LineBundleTwistVanish
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechDMemLocPart
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.FinrankSectionsOverEqH0
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.DegreeOneCellEqChartUpdate
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AltSumEqOfEventually
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTer
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XMemMIdealOverIff
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocAtRatio
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XBaseMemMIdealOverGraph
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemMIdealOverIff
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Imports

@[expose] public section

namespace PositivityTheory.HtPt.Ktw

theorem a0 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CurveComap.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CurveComap.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SectionRatio.full
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RatioDim.full

theorem a6 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.TensorRealises.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.TensorRealises.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelGenerated.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SpanSecs.proof

theorem a7 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.TensorRealise.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.TensorRealise.proof a6

theorem a8 :
    GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.KHCombCyclic.proof
    GroundTheory.Heights₂.Heights.Kleiman.KHCombContract.full

theorem a9 :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSFreeStatement :=
  GroundTheory.Heights₂.Heights.Kleiman.KHTheoremSFree.proof
    GroundTheory.Heights₂.Heights.Kleiman.KHFreeEmbed.full
    GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp.full
    GroundTheory.Heights₂.Heights.Kleiman.KHFreeIndep.full
    GroundTheory.Heights₂.Heights.Kleiman.KHCombContract.full a8
    GroundTheory.Heights₂.Heights.Kleiman.KHFreeBadFinite.full

theorem a10 :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechSESStatement :=
  GroundTheory.Heights₂.Heights.Kleiman.KHCechSES.proof
    GroundTheory.Heights₂.Heights.Kleiman.KHCechDSq.full
    GroundTheory.Heights₂.Heights.Kleiman.KHCechDDeg.full

theorem a11 :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement :=
  GroundTheory.Heights₂.Heights.Kleiman.KHTheoremS.proof a9 a10
    GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt.full

theorem a12 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerPoly.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerPoly.proof a11
    GroundTheory.Heights₂.Heights.Swarm.EulerVar.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.PolyOfDiffsExact.full

theorem a13 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.MultiSerre.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.MultiSerre.proof a11
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SectionMapInj.full

theorem a14 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelRowExact.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelRowExact.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSub.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellZeroConst.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowSecGlue.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellContract.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocGlue.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowChartAct.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RowLocCover.closed

theorem a15 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelCechRefine.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelCechRefine.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CechContract.proof a14
    GroundTheory.Heights₂.Heights.Swarm.DoubleCech.proof

theorem a16 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RayVanish.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.RayVanish.proof_of_ties
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval.proof a15

theorem a17 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SectionsPoly.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SectionsPoly.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.HZeroRowPlaceData.full a12 a13 a16

theorem a18 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NumModel.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NumModel.proof a7 a17
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelDim.proof

theorem a19 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.DegEq.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.DegEq.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.GraphRestrict.full a5 a18

theorem a20 :
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefEq.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefEq.proof a0
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CurveLift.full a19

end PositivityTheory.HtPt.Ktw
