module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder
public import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.CyclotomicNorms.StatementI
public import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes

@[expose] public section

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dirichletLZerosInWindow_finite_and_pos_order : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ), (zerosIn χ t T).Finite ∧ ∀ ρ ∈ zerosIn χ t T, 1 ≤ zmult χ ρ := by
  first | exact @GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult | exact GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult | (intros; apply GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult <;> assumption)
