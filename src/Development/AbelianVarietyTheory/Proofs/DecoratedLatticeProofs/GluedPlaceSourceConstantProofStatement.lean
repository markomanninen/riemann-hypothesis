module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceSourceConstantProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedPlaceSourceConstant_proof : ∀ D : D7, GlobalTheory.FinPl.SourceExact D := by
  first | exact @GlobalTheory.FinPl.sourceExact | exact GlobalTheory.FinPl.sourceExact | (intros; apply GlobalTheory.FinPl.sourceExact <;> assumption)
