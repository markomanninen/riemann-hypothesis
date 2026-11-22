module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEigenReal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_eigen_real : PositivityTheory.Rg.BcB.F.Tail.PExp.TensEigR := by
  first | exact @GlobalTheory.CompanionTheory.TensEigSecond.tensEigR | exact GlobalTheory.CompanionTheory.TensEigSecond.tensEigR | (intros; apply GlobalTheory.CompanionTheory.TensEigSecond.tensEigR <;> assumption)
