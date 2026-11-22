module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.InterSumEventuallyEqInterNum
public import Development.WeilBound.CoreStatements.HodgeTatePoints.SnapperHyperplane
public import Development.WeilBound.CoreStatements.HodgeTatePoints.InterNumPointDeg

@[expose] public section

namespace PositivityTheory.HtPt.Kra

universe u w

theorem kleiman_input : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{u, w} :=
  GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.proof interNumEventual interNumAdditive
    (intersectionNumberCut_of_mixedTwistShift mixedTwistShift) interNumPointDeg

theorem kleiman_input_universe_zero : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0} := kleiman_input

end PositivityTheory.HtPt.Kra
