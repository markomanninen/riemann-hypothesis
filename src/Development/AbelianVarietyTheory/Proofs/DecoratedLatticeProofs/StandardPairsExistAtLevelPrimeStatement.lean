module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairsExistAtLevelPrime
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairs_exist_at_levelPrime : GlobalTheory.AdForm.StdEx' := by
  first | exact @GlobalTheory.AdForm.StdExProof.stdEx' | exact GlobalTheory.AdForm.StdExProof.stdEx' | (intros; apply GlobalTheory.AdForm.StdExProof.stdEx' <;> assumption)
