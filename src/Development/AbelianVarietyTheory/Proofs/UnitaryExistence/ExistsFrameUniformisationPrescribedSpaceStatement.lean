module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameUniformisationPrescribedSpace
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
theorem _root_.GlobalTheory.T.exists_frameUniformisation_prescribedSpace : N1c → GlobalTheory.Published.HasseNormSt → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), 1 ≤ Dw.p + Dw.q → GoodEmb c σ → cc ξ₀ = -ξ₀ → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → ∃ U : Unf Xo c σ r, IsUnf U ∧ Nonempty U.Comp ∧ (∀ k la γ, (U.X k).χ la γ = 1) ∧ (∀ k, (U.X k).Gm = Gm ∧ (U.X k).ξ0 = ξ₀) ∧ (∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x)) ∧ ∀ ρ, FJ.LatZ U.X ρ ∧ (l.A = 1 → FJ.ExpoMatch U.X 1 ρ l.M) := by
  first | exact @GlobalTheory.FrameUnif.exists_unf_of_space | exact GlobalTheory.FrameUnif.exists_unf_of_space | (intros; apply GlobalTheory.FrameUnif.exists_unf_of_space <;> assumption)
