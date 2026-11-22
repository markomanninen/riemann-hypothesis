module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledLatticePrimitiveIsotropicFrameCompletion
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledLattice_primitive_isotropic_frame_completion : Completion := by
  first | exact @GlobalTheory.FrameCompletion.completion | exact GlobalTheory.FrameCompletion.completion | (intros; apply GlobalTheory.FrameCompletion.completion <;> assumption)
