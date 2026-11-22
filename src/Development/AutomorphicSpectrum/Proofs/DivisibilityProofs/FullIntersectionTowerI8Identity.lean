module

public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.GoodTowerAntisymmetry
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProportionalStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreePolynomialEvalStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AntisymmetryStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelExistsOfGivenStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricExistsOfGivenStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelArithDimensionBoundaryStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverRealisationPullbackStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagXdegStatement
public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem full_intersection_tower_I8_relation : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I8 II (hhFl (CMType H) (D.p + D.q) II) :=
  @SquareStatements.good_tower_antisymmetry

end GlobalTheory.CompanionTheory.Ar.Top
