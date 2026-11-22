module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthogonalAnisotropicFrameBoundedCM
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle

@[expose] public section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalAnisotropicFrame_bounded_CM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], FrameSmall E := by
  first | exact @GlobalTheory.SmoothForms.frameSmall | exact GlobalTheory.SmoothForms.frameSmall | (intros; apply GlobalTheory.SmoothForms.frameSmall <;> assumption)
