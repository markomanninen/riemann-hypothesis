module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumAtSplitPlacesProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeeSawDatumAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.LastTAll D := by
  first | exact @GlobalTheory.LastTAllPf.main | exact GlobalTheory.LastTAllPf.main | (intros; apply GlobalTheory.LastTAllPf.main <;> assumption)
