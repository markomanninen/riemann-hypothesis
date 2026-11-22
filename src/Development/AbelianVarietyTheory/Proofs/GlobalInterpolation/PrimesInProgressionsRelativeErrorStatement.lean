module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesInProgressionsRelativeError
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primesInProgressions_relativeError : GlobalTheory.Lin.PrimesRel := by
  first | exact @GlobalTheory.Lin.primesRel_holds | exact GlobalTheory.Lin.primesRel_holds | (intros; apply GlobalTheory.Lin.primesRel_holds <;> assumption)
