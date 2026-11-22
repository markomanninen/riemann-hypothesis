module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleKroneckerPowerTranspose
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completelyReducible_kroneckerPower_transpose : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∀ n : ℕ, SS ((fun g => (tpow n g)ᵀ) '' Γ) := by
  first | exact @GlobalTheory.ClassFin.ss_tpow_transpose | exact GlobalTheory.ClassFin.ss_tpow_transpose | (intros; apply GlobalTheory.ClassFin.ss_tpow_transpose <;> assumption)
