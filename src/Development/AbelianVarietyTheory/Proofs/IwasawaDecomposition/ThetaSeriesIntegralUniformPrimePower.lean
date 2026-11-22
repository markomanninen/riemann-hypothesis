module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SerIntAtOfSeriesRat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsTowerCoverStatement

@[expose] public section

namespace GlobalTheory

theorem serInt_outright : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP
  exact ⟨fun u hu c0 hc0 => GlobalTheory.LevelSeries.serIntAt_record D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP u hu c0 hc0, GlobalTheory.T.unramified_descent_integral_forms_tower_cover D G Pl0 T0 A T R F κ v₀ hL hμ hG hF hM hT hTie i hS hV hFP⟩

end GlobalTheory
