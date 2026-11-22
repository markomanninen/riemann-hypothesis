module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevSpacePreserved
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_space_preserved : PositivityTheory.RgBcC.Fc.PresSob := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.presSob | exact GlobalTheory.CompanionTheory.PresSobA.presSob | (intros; apply GlobalTheory.CompanionTheory.PresSobA.presSob <;> assumption)
