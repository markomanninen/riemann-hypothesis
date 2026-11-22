module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionByZeroAtSplitPlacesProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extensionByZeroAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.ExtAll D := by
  first | exact @GlobalTheory.FinPl.ExtAllPf.ext_all | exact GlobalTheory.FinPl.ExtAllPf.ext_all | (intros; apply GlobalTheory.FinPl.ExtAllPf.ext_all <;> assumption)
