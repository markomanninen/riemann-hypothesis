module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationModel

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

theorem frame_lieModel_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (u : Fin n → ℂ), ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left) :=
  @PositivityTheory.Xgn.quotient_uniformization_model

end GlobalTheory.CompanionTheory.Ar.QuotUnif
