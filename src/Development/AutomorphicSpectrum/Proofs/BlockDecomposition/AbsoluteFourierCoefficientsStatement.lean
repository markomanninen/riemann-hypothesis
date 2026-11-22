module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteFourierCoefficients
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absolute_fourier_coefficients : PositivityTheory.RgBcC.Fc.AbsFC := by
  first | exact @GlobalTheory.CompanionTheory.FuncCalc.absFC | exact GlobalTheory.CompanionTheory.FuncCalc.absFC | (intros; apply GlobalTheory.CompanionTheory.FuncCalc.absFC <;> assumption)
