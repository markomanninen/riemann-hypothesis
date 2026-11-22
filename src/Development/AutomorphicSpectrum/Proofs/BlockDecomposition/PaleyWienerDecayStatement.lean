module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PaleyWienerDecay
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.paley_wiener_decay : PositivityTheory.RgBcC.Fc.PWdecay := by
  first | exact @GlobalTheory.CompanionTheory.WaveCurve.Decay.pwdecay | exact GlobalTheory.CompanionTheory.WaveCurve.Decay.pwdecay | (intros; apply GlobalTheory.CompanionTheory.WaveCurve.Decay.pwdecay <;> assumption)
