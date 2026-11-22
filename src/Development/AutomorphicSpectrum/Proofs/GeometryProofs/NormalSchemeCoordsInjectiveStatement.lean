module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalSchemeCoordsInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_scheme_coords_injective : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ q : X, genPt ξ ⤳ q) → ∀ (z z' : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → CoordsAt ξ y z' w → z = z' := by
  exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.point_eq_of_coordsAt
