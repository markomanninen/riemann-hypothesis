module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealConditions
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginWeightIdentityStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_real_conditions : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ B a, (T.M B a).EffDiff T.nu := by
  intro _ E _ _ _ _ H D Xo l c Y _ T o _ _ _ _ _ _ B a
  obtain ⟨n₀, N₀, hn, _, hne, hmem⟩ := GlobalTheory.T.root_origin_weight_identity
    E H D l (Xo l) c _ _ Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) T.nu (o.nu_eq a)
  let s : (T.M B a).Ω := (N₀ : (T.M B a).Ω) * (o.Or B a).g (o.Fx a).sE *
    ∏ r, (o.Or B a).e r ^ (o.Fx a).n r
  refine ⟨(o.Fx a).kA * (o.Fx a).q', n₀, Nat.mul_pos ?_ (o.Fx a).q'_pos, hn, s, hne, hmem⟩
  rw [← (o.Or B a).kA_eq]
  exact (T.M B a).kA_pos
