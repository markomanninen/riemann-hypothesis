module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteCutoffBound
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolute_cutoff_bound : PositivityTheory.RgBcC.Fc.AbsCut := by
  first | exact @GlobalTheory.CompanionTheory.FcCut.absCut | exact GlobalTheory.CompanionTheory.FcCut.absCut | (intros; apply GlobalTheory.CompanionTheory.FcCut.absCut <;> assumption)
