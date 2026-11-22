module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsCompactifiedModel
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeMetricFrameProperties
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRegularizationSettingStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRegularizationOfHodgeMetricStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemWeightLeftStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionPositiveStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionLimitStatement

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.cusp_weight_regularisations_tied : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd), ∃ (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc) (S : LogLogRegularisationSetting M Dc.Xo (muLine Hd)) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)), Or.𝔐.IsCuspWeight Or.sm U ∧ (∀ z, 0 ≤ U z) ∧ (∀ z ∈ Dc.Xo, ∀ t : K → ℂ, (∀ k, t k ≠ 0) → U (torusSmul t z) = U z) ∧ S.IsTied ∧ S'.IsTied ∧ ConjU S' := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or
  obtain ⟨U, hU, h0, hT, hC, -⟩ := GlobalTheory.T.intersection_system_weight_left hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or
  obtain ⟨hp1, -, hp2, hc2⟩ := GlobalTheory.T.cusp_intersection_positive hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or U hU
  obtain ⟨hb, -⟩ := GlobalTheory.T.cusp_chart_log_growth_bounds hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or U hU
  obtain ⟨-, -, hL, hO⟩ := GlobalTheory.CompanionTheory.Relay.hodge_metric_frame_properties K J II (CMType H) Ω W Dc Hd
  obtain ⟨M⟩ := GlobalTheory.CompanionTheory.Relay.exists_compactified_model K J II (CMType H) Ω W Dc
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_regularization_of_hodge_metric K J II (CMType H) Ω W Dc Hd M hp1
  obtain ⟨S', hS', hJ⟩ := GlobalTheory.T.exists_regularization_setting K J II (CMType H) Ω W Dc Hd M (corrW Hd U)
    (fun z hz a ha => by
      have := hL z hz a ha
      simp only [corrW, hT z a ha, this]
      ring)
    hp2 hc2 hb
    (fun z hz => by
      have := hO z hz
      simp only [corrW, hC z, this])
  exact ⟨U, M, S, S', hU, h0, fun z _ t ht => hT z t ht, hS, hS', hJ⟩
