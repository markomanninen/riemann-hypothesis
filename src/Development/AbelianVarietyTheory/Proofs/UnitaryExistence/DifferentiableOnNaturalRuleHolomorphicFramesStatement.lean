module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnNaturalRuleHolomorphicFrames
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
theorem _root_.GlobalTheory.T.differentiableOn_natural_rule_holomorphic_frames : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (p : TRing c.F) (y₀ : FrPt Xo c p.R) (ψ : V → (p.R →ₐ[c.F] CAt σ)) (z y : V → FrPt Xo c (CAt σ)) (G : V → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : V → CAt σ), (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b)) → (∀ t, DifferentiableOn ℂ (fun b => toC (ψ b t)) B) → (∀ τ i j, DifferentiableOn ℂ (fun b => toC (G b τ i j)) B) → DifferentiableOn ℂ (fun b => toC (a b)) B → ∀ w n, ∀ f ∈ sec Xo c w n, DifferentiableOn ℂ (fun b => toC (evR Xo c f (y b))) B := by
  first | exact @GlobalTheory.HolEval.differentiableOn_evR | exact GlobalTheory.HolEval.differentiableOn_evR | (intros; apply GlobalTheory.HolEval.differentiableOn_evR <;> assumption)
