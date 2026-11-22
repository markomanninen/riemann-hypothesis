module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelPurity
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity

@[expose] public section

namespace GlobalTheory

theorem regularAlgebraicPurity_of_clozel (hP : GlobalTheory.Published.ClozelPurity) (hC : GlobalTheory.Published.ClozelCohomological) :
    GlobalTheory.Published.RegularAlgebraicPurity := by
  intro E _ _ _ a ha π hr
  exact ⟨hP E a ha π fun τ => (hr τ).2, hC E a ha π hr⟩

end GlobalTheory
