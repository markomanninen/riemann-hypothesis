module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffDetMemSpanDetIntegralPolynomialVectors
public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_det_mem_span_det_integral_polynomial_vectors : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (M : Submodule (𝓞 F) V) (d : ℕ) (b : Module.Basis (Fin d) F V) (τ : Type) (P : Matrix (Fin d) (Fin d) (MvPolynomial τ F)), (∀ k m, ∑ i, AddMonoidAlgebra.coeff (P i k) m • b i ∈ M) → ∀ m, AddMonoidAlgebra.coeff P.det m ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ M) ∧ y = b.det v} := by
  first | exact @GlobalTheory.DetCoeff.coeff_det_mem_span_det | exact GlobalTheory.DetCoeff.coeff_det_mem_span_det | (intros; apply GlobalTheory.DetCoeff.coeff_det_mem_span_det <;> assumption)
