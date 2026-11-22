module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralOfEpsteinConv
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

@[expose] public section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_integral_of_epstein_conv : EpConv → ZetaK := by
  first | exact @GlobalTheory.CompanionTheory.ZetaAlongK.zetaK | exact GlobalTheory.CompanionTheory.ZetaAlongK.zetaK | (intros; apply GlobalTheory.CompanionTheory.ZetaAlongK.zetaK <;> assumption)
