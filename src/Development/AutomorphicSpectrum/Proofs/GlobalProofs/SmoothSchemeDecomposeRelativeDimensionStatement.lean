module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothSchemeDecomposeRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactSpacePts
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_scheme_decompose_relative_dimension : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ), Smooth s → ∃ W : ℕ → X.Opens, (∀ D, IsClosed (W D : Set X)) ∧ (∀ D, SmoothOfRelativeDimension D ((W D).ι ≫ s)) ∧ (⨆ D, W D) = ⊤ ∧ Pairwise fun D D' => W D ⊓ W D' = ⊥ := by
  first | exact @GlobalTheory.CompanionTheory.Gaga.exists_clopen_smoothOfRelativeDimension | exact GlobalTheory.CompanionTheory.Gaga.exists_clopen_smoothOfRelativeDimension | (intros; apply GlobalTheory.CompanionTheory.Gaga.exists_clopen_smoothOfRelativeDimension <;> assumption)
