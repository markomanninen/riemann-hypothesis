module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsValueOverPoint
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constants_value_over_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X), IsOver 𝔐 z κ p → ∀ x : c.F, ValAt 𝔐.ξ z (𝔐.cst x) (κ x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.val_cst | exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.val_cst | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.val_cst <;> assumption)
