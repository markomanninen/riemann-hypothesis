module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemGeneralLemmaOrderOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm

@[expose] public section

open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveSystem_generalLemma_orderOne : GLOnto 1 ∧ GLCount 1 := by
  first | exact @GlobalTheory.PMonE.gl1 | exact GlobalTheory.PMonE.gl1 | (intros; apply GlobalTheory.PMonE.gl1 <;> assumption)
