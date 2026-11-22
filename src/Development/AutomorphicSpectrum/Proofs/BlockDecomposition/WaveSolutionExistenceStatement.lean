module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_solution_existence : PositivityTheory.RgBcC.AsmEx := by
  first | exact @GlobalTheory.CompanionTheory.WaveAll.asmEx | exact GlobalTheory.CompanionTheory.WaveAll.asmEx | (intros; apply GlobalTheory.CompanionTheory.WaveAll.asmEx <;> assumption)
