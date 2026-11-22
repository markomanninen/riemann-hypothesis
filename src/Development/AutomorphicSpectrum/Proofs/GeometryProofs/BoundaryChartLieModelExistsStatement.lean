module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLieModelExists
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_chart_lie_model_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (u : Fin n → ℂ), ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.frame_lieModel_fibre | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.frame_lieModel_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.frame_lieModel_fibre <;> assumption)
