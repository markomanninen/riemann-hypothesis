module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeFrobeniusKernelMulSpanPrimePowers
public import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_le_frobeniusKernel_mul_span_primePowers : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [Module.Finite K H] (r : ℕ), Module.finrank K H ≤ Module.finrank K (H ⧸ frobKerIdeal (p ^ r) K H) * Module.finrank K (Submodule.span K (Set.range fun a : H => a ^ p ^ r)) := by
  first | exact @GlobalTheory.PDiv.finrank_le_frobKer_mul_span_pow | exact GlobalTheory.PDiv.finrank_le_frobKer_mul_span_pow | (intros; apply GlobalTheory.PDiv.finrank_le_frobKer_mul_span_pow <;> assumption)
