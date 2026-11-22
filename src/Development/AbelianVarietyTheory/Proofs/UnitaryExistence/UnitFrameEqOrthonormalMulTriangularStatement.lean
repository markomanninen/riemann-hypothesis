module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
public import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitFrame_eq_orthonormal_mul_triangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E), (∀ a b, cc (Gm a b) = Gm b a) → (∀ x ∈ GG Ψ Gm p0, (∀ τ i, ‖dmin Gm x τ i‖ = 1) → ∃ x₀ : Frame Ψ r, ∃ b ∈ Bor Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∀ τ i, ‖b τ i i‖ = 1) ∧ x = rmul x₀ b) ∧ (∀ x₀ : Frame Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → x₀ ∈ GG Ψ Gm p0 ∧ ∀ τ i, ‖dmin Gm x₀ τ i‖ = 1) ∧ ∀ (τ : E →+* ℂ) (u x₀ : Matrix (Fin r) (Fin r) ℂ), uᵀ * Gm.map τ * u.map (starRingEnd ℂ) = Gm.map τ → gram τ Gm (u * x₀) = gram τ Gm x₀ := by
  first | exact @GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular | exact GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular | (intros; apply GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular <;> assumption)
