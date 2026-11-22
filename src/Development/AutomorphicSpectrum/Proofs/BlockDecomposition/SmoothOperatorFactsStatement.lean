module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothOperatorFacts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_operator_facts : PositivityTheory.RgBcC.Fc.SmoothOp := by
  first | exact @GlobalTheory.CompanionTheory.FcSmooth.smoothOp | exact GlobalTheory.CompanionTheory.FcSmooth.smoothOp | (intros; apply GlobalTheory.CompanionTheory.FcSmooth.smoothOp <;> assumption)
