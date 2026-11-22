module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LbSpreads
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_spreads_out' : GlobalTheory.SpreadingModels.LBSpreads := by
  first | exact @GlobalTheory.CompanionTheory.LBLimit.lbSpreads | exact GlobalTheory.CompanionTheory.LBLimit.lbSpreads | (intros; apply GlobalTheory.CompanionTheory.LBLimit.lbSpreads <;> assumption)
