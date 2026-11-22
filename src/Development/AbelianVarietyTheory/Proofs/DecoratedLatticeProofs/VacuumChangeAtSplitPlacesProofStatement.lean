module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumChangeAtSplitPlacesProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumChangeAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.RebaseAll D := by
  first | exact @GlobalTheory.FinPl.RebaseProof.rebaseAll | exact GlobalTheory.FinPl.RebaseProof.rebaseAll | (intros; apply GlobalTheory.FinPl.RebaseProof.rebaseAll <;> assumption)
