module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupCosetDecomposition
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroup_coset_decomposition : Ad3.R.C1 := by
  first | exact @GlobalTheory.CompanionTheory.RankinStepC.c1 | exact GlobalTheory.CompanionTheory.RankinStepC.c1 | (intros; apply GlobalTheory.CompanionTheory.RankinStepC.c1 <;> assumption)
