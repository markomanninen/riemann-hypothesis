module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorNormal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_operator_normal : PositivityTheory.RgBcC.GelN := by
  first | exact @GlobalTheory.CompanionTheory.GelLevi.gelN | exact GlobalTheory.CompanionTheory.GelLevi.gelN | (intros; apply GlobalTheory.CompanionTheory.GelLevi.gelN <;> assumption)
