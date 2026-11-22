module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SourceLiftAtGluedPlaceProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sourceLiftAtGluedPlace_proof : ∀ D : D7, GlobalTheory.FinPl.SourceGlued D := by
  first | exact @GlobalTheory.FinPl.sourceGlued | exact GlobalTheory.FinPl.sourceGlued | (intros; apply GlobalTheory.FinPl.sourceGlued <;> assumption)
