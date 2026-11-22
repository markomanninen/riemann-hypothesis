module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairsAmplitudeBoundOfTypeBound
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TermSumBoundOfPairsAmplitude

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairsAmplitudeBound_of_typeBound : GlobalTheory.Core.Deg.PairsDegOfType := by
  first | exact @GlobalTheory.Core.Deg.pairsDegOfType_holds | exact GlobalTheory.Core.Deg.pairsDegOfType_holds | (intros; apply GlobalTheory.Core.Deg.pairsDegOfType_holds <;> assumption)
