module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusCurve
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functional_calculus_curve : PositivityTheory.RgBcC.Fc.Fcurve := by
  first | exact @GlobalTheory.CompanionTheory.WaveCurve.fcurve | exact GlobalTheory.CompanionTheory.WaveCurve.fcurve | (intros; apply GlobalTheory.CompanionTheory.WaveCurve.fcurve <;> assumption)
