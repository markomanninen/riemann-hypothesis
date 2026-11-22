module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermConvergence
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

@[expose] public section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_term_convergence : EpConv → TestSph → Lines → Term → SideConv := by
  first | exact @GlobalTheory.CompanionTheory.RgEisSide.sideConv | exact GlobalTheory.CompanionTheory.RgEisSide.sideConv | (intros; apply GlobalTheory.CompanionTheory.RgEisSide.sideConv <;> assumption)
