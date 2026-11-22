module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningGradedVanishNegativeStatement

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

theorem gr_neg_van : ∀ {b : Base} (L : b.Fun) (Q : ObjectProperty (Thick L)) (r : ℤ), r < 0 → ∀ j : ℕ,
    Subsingleton (HU (gr (Φ := thP L) (thFil L) r) Q j) := GlobalTheory.T.thickening_graded_vanish_negative

end CrystallineSemistableComparison.Pb
