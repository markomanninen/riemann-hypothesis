module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusFirstAssumption
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functional_calculus_first_assumption : PositivityTheory.RgBcC.Fc.Asm1 := by
  first | exact @GlobalTheory.CompanionTheory.WaveFc.Asm.asm1 | exact GlobalTheory.CompanionTheory.WaveFc.Asm.asm1 | (intros; apply GlobalTheory.CompanionTheory.WaveFc.Asm.asm1 <;> assumption)
