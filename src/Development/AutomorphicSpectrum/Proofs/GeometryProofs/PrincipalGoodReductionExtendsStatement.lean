module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalGoodReductionExtends
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObject
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ModuliNonemptyOfObj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalDim

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_good_reduction_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → (∀ (σ : L →+* ℂ) (τ : 𝓞 E →+* ℂ), LieMult t.act (spMap σ) τ 0) → ∃ t' : SAB H (Sp (𝓞 L)), Nonempty (SABMap t t' (spMap (algebraMap (𝓞 L) L))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TrivialModel.exists_model_of_rank_zero | exact GlobalTheory.CompanionTheory.Ar.TrivialModel.exists_model_of_rank_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.TrivialModel.exists_model_of_rank_zero <;> assumption)
