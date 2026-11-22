module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasselmanWallachAdmissible
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.DerivativeRepresentation
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirNonnegative
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MatrixActionAdditive
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.HighestWeightKernel
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C3B
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C3C
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.KTypesFiniteOfHighestWeight
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.DerivativeContinuity
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.Imports
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ZeroOnDense
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C7
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SlopeLimitConstant
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.PageTheorem
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ZetaClassicalZeroFreeRegion
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.TendstoPiZero
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.D5
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExistsFunctional
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExponentialKSet
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.BilinearFormCasimir
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenOrthogonalForm
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SeminormApproximation
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirNonnegativeSymmetric
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MatrixActionLinear
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.HilbertSchmidtSqEq
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenspacesOrthogonal
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.E3D

@[expose] public section

namespace PositivityTheory.CW

theorem lift_of (hM : MaxPr) : GlobalTheory.Published.CasselmanWallachLift := by
  have hmodel := model_of c1 c2a c2b c3a c3b (k_types_finite_of_highest_weight c3c)
  exact lift_of_steps hM hmodel c4 c5 c6 c7 d0 d1b d2 d3 d4b d5

theorem cw_of (hM : MaxPr) : GlobalTheory.Published.CasselmanWallach := by
  have hmodel := model_of c1 c2a c2b c3a c3b (k_types_finite_of_highest_weight c3c)
  exact cw_of_steps hM hmodel c5 d0 (lift_of hM) e1a e1b e2a e2b e2c e2d e3a e3b e3c e3d

end PositivityTheory.CW
