module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOut
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_spreads_out : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads | exact GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads | (intros; apply GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads <;> assumption)
