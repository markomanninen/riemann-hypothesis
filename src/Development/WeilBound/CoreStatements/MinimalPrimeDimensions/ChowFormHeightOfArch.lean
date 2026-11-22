module

public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.IsClosedOfCoheight
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.DescEval
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.SumNormSqUnitary
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.FormHeightOneEq
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.StCharts
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ChowDegreeSection
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly

@[expose] public section

namespace ChowFormHeightComparison₂.CF

open GroundTheory.Heights₂.Heights in
theorem chowFormHeight_of_arch (hA : StArch) (hM : MahlerSection.Statement) (hE : GlobalTheory.Published.ArExists) :
    PositivityTheory.UnitarySelfGeneration.ChowFormHeight :=
  glue (stMain_of (stVert stPts stPull stDiv) hA
    (ChowHeightRecursion.of_leaves ChowFormSectionVertical.full hM ChowFormBaseChange.full BaseChangeAvoid.full)
    ChowFormSection.full ChowHeightMul.full ProjPrimeHasPoint.full) stModel stForm hE

end ChowFormHeightComparison₂.CF
