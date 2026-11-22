module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorsCommute
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_operators_commute : PositivityTheory.RgBcC.GelComm := by
  first | exact @GlobalTheory.CompanionTheory.GelC.gelComm | exact GlobalTheory.CompanionTheory.GelC.gelComm | (intros; apply GlobalTheory.CompanionTheory.GelC.gelComm <;> assumption)
