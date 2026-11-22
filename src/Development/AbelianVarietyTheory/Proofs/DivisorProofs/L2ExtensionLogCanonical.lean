module

public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFrameOffFiniteZeroSetStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ExtensionEtaleCoordinatesFiniteZerosStatement

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem l2ExtensionLogCanonical' : GlobalTheory.Published.L2ExtensionLogCanonical := by
  intro n hn Y _ _ _ _ _ _ ι La _ A hH E L s hs hS hjac hle δ hδ hcurv f
  obtain ⟨Λ, τ, z, β, hdata⟩ := GlobalTheory.T.exists_etale_frame_off_finite_zeroSet n Y ι La A hn hH E L s hs hS
  exact GlobalTheory.T.l2_extension_etale_coordinates_finite_zeros n Y ι La A hn E L s hs hS hjac hle δ hδ hcurv Λ τ z β hdata f

end GlobalTheory
