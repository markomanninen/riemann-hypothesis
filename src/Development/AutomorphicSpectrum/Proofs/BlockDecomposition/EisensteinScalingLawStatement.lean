module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinScalingLaw
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_scaling_law : PositivityTheory.RgEis.Scale := by
  first | exact @GlobalTheory.CompanionTheory.RgEisScale.scale | exact GlobalTheory.CompanionTheory.RgEisScale.scale | (intros; apply GlobalTheory.CompanionTheory.RgEisScale.scale <;> assumption)
