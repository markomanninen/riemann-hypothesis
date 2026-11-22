module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.CoefficientMapHeightBound
public import Formalism.LocalToGlobal.Columns.FactorialSumLePowMulProd
public import Formalism.LocalToGlobal.Columns.CoefColLemmas

@[expose] public section

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.L2.Forms

section Main

variable (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

end Main

section Mono

theorem fock_norm_rational_eq {σ : Type} (P : MvPolynomial σ ℚ) : fockN (map (algebraMap ℚ ℂ) P) = ((Formalism.GradedWeylDivisibility.fockQ P P : ℚ) : ℝ) := by
  unfold fockN Formalism.GradedWeylDivisibility.fockQ
  rw [support_map_of_injective _ (algebraMap ℚ ℂ).injective]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_map, mfact]
  have : ‖(algebraMap ℚ ℂ) (AddMonoidAlgebra.coeff P m)‖ ^ 2 = ((AddMonoidAlgebra.coeff P m : ℚ) : ℝ) * ((AddMonoidAlgebra.coeff P m : ℚ) : ℝ) := by
    rw [eq_ratCast, Complex.norm_ratCast, sq_abs]
    ring
  rw [this]
  push_cast
  rfl

variable {ι : Type} [Fintype ι] {n : ℕ}

end Mono

section Gen

open Formalism.HermitianLattices.TraceIntegrality

variable (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {ι : Type} [Fintype ι]

end Gen

end Formalism.L2.Col
