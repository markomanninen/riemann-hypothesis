module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theoremOfCubeAbelianScheme_over_arbitrary_base : GlobalTheory.Published.CubeTheorem := by
  first | exact @GlobalTheory.CubeTop.cubeTheorem | exact GlobalTheory.CubeTop.cubeTheorem | (intros; apply GlobalTheory.CubeTop.cubeTheorem <;> assumption)
