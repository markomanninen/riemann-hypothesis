module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsHermitianLogOfPosDefGram
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isHermitianLogOfPosDef_gram : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x : Matrix ι ι ℂ), IsUnit x.det → ∃ H : Matrix ι ι ℂ, IsLog H (xᴴ * x) := by
  first | exact @GlobalTheory.ClassFin.exists_isLog_gram | exact GlobalTheory.ClassFin.exists_isLog_gram | (intros; apply GlobalTheory.ClassFin.exists_isLog_gram <;> assumption)
