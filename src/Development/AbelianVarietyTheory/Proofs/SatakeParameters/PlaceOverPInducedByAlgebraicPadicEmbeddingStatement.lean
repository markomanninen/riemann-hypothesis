module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceOverPInducedByAlgebraicPadicEmbedding
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypotheses

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_over_p_induced_by_algebraic_padic_embedding : GlobalTheory.DatumJets.PlaceAbove := by
  first | exact @GlobalTheory.DatumJets.Place.placeAbove | exact GlobalTheory.DatumJets.Place.placeAbove | (intros; apply GlobalTheory.DatumJets.Place.placeAbove <;> assumption)
