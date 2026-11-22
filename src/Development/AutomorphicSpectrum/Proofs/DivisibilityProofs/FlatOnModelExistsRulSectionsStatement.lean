module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlatOnModelExistsRulSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_on_model_exists_rul_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Formalism.L2.Pj.Comp Xo c) (Z' : CptOver Y (Z : Set (Xo.XF c))) (τ : GlobalTheory.AllWt.Psi H) (φ : FrameFn Xo c), FlatOnModel Z' τ.1 φ → ∃ s s' : Formalism.L2.Pj.Rul Xo c, s ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) ∧ s' ∈ GlobalTheory.AllWt.secZ Xo c (-GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * s' = s' ∧ s * s' = GlobalTheory.FlatLine.idem Z ∧ Reads (Z : Set (Xo.XF c)) τ.1 s φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.exists_flat_sec | exact GlobalTheory.CompanionTheory.Ar.Br.exists_flat_sec | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.exists_flat_sec <;> assumption)
