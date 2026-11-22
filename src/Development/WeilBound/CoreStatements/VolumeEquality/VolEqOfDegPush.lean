module

public import Development.WeilBound.CoreStatements.VolumeEquality.VolEqOf
public import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifEx2
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.WeilBound.CoreStatements.VolumeEquality.HolNull
public import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeets
public import Development.WeilBound.CoreStatements.VolumeEquality.CoverRoots
public import Development.WeilBound.CoreStatements.VolumeEquality.LocInj
public import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnif
public import Development.WeilBound.CoreStatements.VolumeEquality.OnePiece
public import Development.WeilBound.CoreStatements.VolumeEquality.BallVol
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

theorem SheetDecomposition.volEq_of_degPush (h : SheetDecomposition.DegPush) : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.q → 3 * D.q + 1 ≤ D.p + D.q → T.VolEq :=
  SheetDecomposition.volEq_of SheetDecomposition.holNull SheetDecomposition.chartMeets SheetDecomposition.rootBranches SheetDecomposition.coverRoots SheetDecomposition.locInj SheetDecomposition.baseUnifEx2 SheetDecomposition.onePiece
    SheetDecomposition.ballVolEq h
