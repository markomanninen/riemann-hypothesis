module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightComparisonBetweenModels
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_comparison_between_models : Top.Given → PtsIntegrableStatement →
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem)
      (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
      (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
      (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M M' : XModel D)
      (S : LogLogRegularisationSetting M D.Xo (muLine Hd))
      (S₁ : LogLogRegularisationSetting M' D.Xo (muLine Hd)) (B : ℕ),
      IsFullIntersectionSystem II → S.IsTied → S₁.IsTied →
      ArLimExists Hd S B ∧ arLim Hd S B = arLim Hd S₁ B := by
  intro hG _ K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M M' S S₁ B hII hS hS₁
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hNb : IsSmoothHerm (fsHerm J (muTwDeg Hd B)) := PB.StepW.fsHerm_isSmoothHerm K J _
  have h₁ := tendsto_arLimFun hIn.metricLocal S hS B hII _ hNb rfl
  have h₂ := tendsto_arLimFun hIn.metricLocal S₁ hS₁ B hII _ hNb rfl
  exact ⟨⟨_, h₁⟩, by rw [arLim, arLim, h₁.limUnder_eq, h₂.limUnder_eq]⟩
