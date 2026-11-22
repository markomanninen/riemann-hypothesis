module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLatticeInverseIndexOfElementaryDivisors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralLatticeInverseIndex_of_elementaryDivisors : Smith → LatIndex := by
  first | exact @GlobalTheory.InertZeta.latIndex_of_smith | exact GlobalTheory.InertZeta.latIndex_of_smith | (intros; apply GlobalTheory.InertZeta.latIndex_of_smith <;> assumption)
