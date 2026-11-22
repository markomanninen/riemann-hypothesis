module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionFiniteNorm
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_function_finite_norm : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), FracBase β → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → U ∈ irreducibleComponents (Xo.XF c) → Z.IsGeom → FlatOnModel Z τ φ → l.GoodAt p → ∃ t : ℝ, HasFinNorm U τ φ p κ t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.FinGood.finGood | exact GlobalTheory.CompanionTheory.Ar.Br.FinGood.finGood | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.FinGood.finGood <;> assumption)
