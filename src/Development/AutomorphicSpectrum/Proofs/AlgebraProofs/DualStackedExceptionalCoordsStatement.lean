module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalCoords
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChart

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_stacked_exceptional_coords : GroundTheory.Heights₂.Heights.DualStackedExcCoords.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords | exact GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcCoords <;> assumption)
