module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticePrescribedFinitelyManySplitPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_prescribed_finitelyManySplitPlaces : ∀ D : D7, GlobalTheory.FinPl.LatAll D := by
  first | exact @GlobalTheory.LatPresc.latAll | exact GlobalTheory.LatPresc.latAll | (intros; apply GlobalTheory.LatPresc.latAll <;> assumption)
