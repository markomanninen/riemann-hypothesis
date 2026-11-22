module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsoOfThickenings
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_of_thickenings : IsoOfThick := by
  first | exact @GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick | exact GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick | (intros; apply GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick <;> assumption)
