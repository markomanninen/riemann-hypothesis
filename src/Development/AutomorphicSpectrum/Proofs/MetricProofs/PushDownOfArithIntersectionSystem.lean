module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPushDown
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagArith
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagNeZero
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagRatioTrdeg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagRatioFieldEq
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagMinorTrdeg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystem
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystemStatement

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv


open GroundTheory.Heights₂.Heights.LowerBoundFree in
theorem hodgeFlagArith : HodgeFlagArith.Statement :=
  HodgeFlagArith.proof HodgeFlagNeZero.proof
    (HodgeFlagRatioTrdeg.proof HodgeFlagRatioFieldEq.full HodgeFlagMinorTrdeg.proof)

theorem pushDown :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement →
      GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.Statement := fun h =>
  GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.proof (GlobalTheory.T.generic_degree_of_arith_system h) GlobalTheory.CompanionTheory.Ar.Giv.ProjF.pfStep hodgeFlagArith

end GlobalTheory.CompanionTheory.Ar.Giv
