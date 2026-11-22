module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumOverEmbeddingsUnitInvariance
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
theorem _root_.GlobalTheory.T.sum_over_embeddings_unit_invariance : ArithIntersectionSystemStatement → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (θ : (𝓞 F)ˣ), IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, IsSmoothHerm (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ∑ sg : F →+* ℂ, Real.log ‖sg ((θ : 𝓞 F) : F)‖ * ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.sum_log_unit_mul_mass_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Giv.sum_log_unit_mul_mass_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.sum_log_unit_mul_mass_eq_zero <;> assumption)
