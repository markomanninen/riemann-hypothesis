module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeEqGeometricDegree
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegGeomDeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_degree_eq_geometric_degree : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.genDegGeomDeg_of_system | exact GlobalTheory.CompanionTheory.Ar.Giv.genDegGeomDeg_of_system | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.genDegGeomDeg_of_system <;> assumption)
