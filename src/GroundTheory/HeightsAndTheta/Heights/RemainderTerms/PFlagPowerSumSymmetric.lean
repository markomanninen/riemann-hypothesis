module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

theorem FlagPowerSumSymmetric.proof : FlagPowerSumSymmetric.Statement := by
  intro f N k τ w
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [blockPowerSum, map_sum, map_pow, Flag.blockPermute_X]
  exact Equiv.sum_comp (w τ) (fun i => (X (τ, i) : RootRing f N) ^ k)

end RestTerms

end GroundTheory.Heights₂.Heights
