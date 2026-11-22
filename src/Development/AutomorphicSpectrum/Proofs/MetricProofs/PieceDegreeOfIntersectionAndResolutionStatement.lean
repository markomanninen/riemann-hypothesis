module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolution
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piece_degree_of_intersection_and_resolution : ArithIntersectionSystemStatement → ResExistsStatement → PtsIntegrableStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.PieceDegree.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree | exact GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree <;> assumption)
