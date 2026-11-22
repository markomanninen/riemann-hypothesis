module

public import Mathlib
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
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingPieces
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPiecesAdditive
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolutionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegrableOfResolutionStatementStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatementStatement

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem embeddingPieces_of_resK (hA : ArithIntersectionSystemStatement)
    (hR : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) :
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.Statement :=
  have hInt : PtsIntegrableStatement := GlobalTheory.T.points_integrable_of_resolution_statement hR
  have hRes : ResExistsStatement := GlobalTheory.T.resolution_exists_of_resolution_statement hR
  GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingPieces.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.PiecesAdditive.proof hInt)
    (GlobalTheory.T.piece_degree_of_intersection_and_resolution hA hRes hInt)

end GlobalTheory.CompanionTheory.Ar.Giv
