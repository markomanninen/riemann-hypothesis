module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import GroundTheory.HeightsAndTheta.Heights.KernelsRest
public import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblySympl
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLatticeBasis
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexDet
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIsLattice
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexTrans
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealLatticeFG
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLineDegree
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordFirst
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordSiegel
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordWeak
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AltRow
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AltPush
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AltFrob
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Inhabitants
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutCaseCompare
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutPrimeEq
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRestCutTransportFirst
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassArithVar
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootArithVar
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualArithVar
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSmooth
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineLevi
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSemipositive
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PNefOfNonneg
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsConjInvariant
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassLeRoot
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootDivSuppEmpty
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootAnchorNonzero
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootPointConj
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootPointsFinite
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootLogNormBound
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPtsIntegralZeroLowerNE
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PMultiHomogMemCoord
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootHeightNE
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootDense
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassHeightBound
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeBasisExists
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualEmbBijective
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineSemipositive
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineConj
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPointDegCPos
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualCurvePoint
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPointArInt
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPointVertR
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineIndex
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPointLineDegree
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PTelescope
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopSubLattice
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualGeomDegStandard
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopMetricChange
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopLatticeChange
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopStandard
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopBound
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPtsOnPlane
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPtsOfPlane
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdMassAt
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualGeomDegPos
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLineOfLargeDegreeDual

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

theorem CoordConeArithVar.full : CoordConeArithVar.Statement :=
  CoordConeArithVar.proof IntDomainDim.full

theorem GrassArithVar.full : GrassArithVar.Statement := GrassArithVar.proof CoordConeArithVar.full

theorem RootArithVar.full : RootArithVar.Statement := RootArithVar.proof CoordConeArithVar.full

theorem DualArithVar.full : DualArithVar.Statement := DualArithVar.proof CoordConeArithVar.full

theorem FsLineSemipositive.full : FsLineSemipositive.Statement :=
  FsLineSemipositive.proof FsLineSmooth.proof FsLineLevi.proof

theorem RootPointConj.full : RootPointConj.Statement := RootPointConj.proof RootAnchorNonzero.proof

theorem RootPointsFinite.full : RootPointsFinite.Statement :=
  RootPointsFinite.proof RootAnchorNonzero.proof

theorem RootLogNormBound.full : RootLogNormBound.Statement :=
  RootLogNormBound.proof RootAnchorNonzero.proof RootPointConj.full PlueckerKernel.full

theorem RootHeight.full : RootHeight.Statement :=
  RootHeight.proofNE RootArithVar.full RootDivSuppEmpty.proof RootLogNormBound.full
    RootPointsFinite.full PtsIntegralZeroLowerNE.proof MultiHomogMemCoord.proof FsLineSmooth.proof

theorem RootDense.full : RootDense.Statement :=
  RootDense.proof MultiHomogMemCoord.proof RootsOfUnityDense.full

theorem GrassHeightBound.full : GrassHeightBound.Statement :=
  GrassHeightBound.proof GrassArithVar.full RootArithVar.full FsLineSemipositive.full
    NefOfNonneg.proof FsConjInvariant.proof GrassLeRoot.proof RootHeight.full RootDense.full

theorem DualStdMassAt.full : DualStdMassAt.Statement :=
  DualStdMassAt.proof DualPtsOnPlane.proof DualPtsOfPlane.proof

theorem DualPointLineDegree.ofOpen (hVI : VertRIndex.Statement) (hSN : SectionIndexNorm.Statement) :
    DualPointLineDegree.Statement :=
  DualPointLineDegree.proof DualCurvePoint.proof PointDegCPos.proof PointArInt.proof
    (PointVertR.proof hVI hSN) DualLineIndex.proof DualLineSemipositive.proof

theorem DualTopBound.ofOpen (hEnergy : DualMetricEnergy.Statement)
    (hBasis : DualTopBasisChange.Statement) (hStacked : DualTopStacked.Statement)
    (hSDeg : DualStackedDegree.Statement) (hBC : DualStdBaseChange.Statement)
    (hGL : GrassLinesProj.Statement) (hCharts : DualGeomDegCharts.Statement)
    (hGChart : GrassGeomDegChart.Statement) (hMass : ChartMassInvariant.Statement) :
    DualTopBound.Statement :=
  DualTopBound.proof DualLatticeBasisExists.proof DualEmbBijective.proof
    (DualTopMetricChange.proof Telescope.proof hEnergy)
    (DualTopLatticeChange.proof (DualTopSubLattice.proof hBasis hStacked hSDeg))
    (DualTopStandard.proof hBC hGL) (DualGeomDegStandard.proof hCharts hGChart hMass)
    GrassHeightBound.full

theorem DualGeomDegPos.ofOpen (hDeg : DegreeStatement) (hInd : PtsIndepStatement) :
    DualGeomDegPos.Statement :=
  DualGeomDegPos.proof hDeg hInd DualArithVar.full DualLineSemipositive.proof DualPtsOnPlane.proof
    DualStdMassAt.full

theorem LineOfLargeDegreeFromZ.ofOpen (hVI : VertRIndex.Statement) (hSN : SectionIndexNorm.Statement)
    (hEnergy : DualMetricEnergy.Statement)
    (hBasis : DualTopBasisChange.Statement) (hStacked : DualTopStacked.Statement)
    (hSDeg : DualStackedDegree.Statement) (hBC : DualStdBaseChange.Statement)
    (hGL : GrassLinesProj.Statement) (hCharts : DualGeomDegCharts.Statement)
    (hGChart : GrassGeomDegChart.Statement) (hMass : ChartMassInvariant.Statement)
    (hDeg : DegreeStatement) (hInd : PtsIndepStatement) :
    LineOfLargeDegreeFromZ.Statement :=
  LineOfLargeDegreeFromZ.proofDual DualLatticeBasisExists.proof DualEmbBijective.proof
    DualArithVar.full DualLineSemipositive.proof NefOfNonneg.proof DualLineConj.proof
    (DualPointLineDegree.ofOpen hVI hSN)
    (DualTopBound.ofOpen hEnergy hBasis hStacked hSDeg hBC hGL hCharts hGChart hMass)
    (DualGeomDegPos.ofOpen hDeg hInd)

end GroundTheory.Heights₂.Heights
