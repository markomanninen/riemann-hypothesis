module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaplacianPolynomialKillsHarishChandraFinit
public import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
public import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp

@[expose] public section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_laplacianPolynomial_kills_harishChandraFinite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∃ p : Polynomial ℂ, p ≠ 0 ∧ ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, Polynomial.aeval (lapOp E a) p φ = 0 := by
  first | exact @GlobalTheory.GLPoly.exists_poly_formsGL | exact GlobalTheory.GLPoly.exists_poly_formsGL | (intros; apply GlobalTheory.GLPoly.exists_poly_formsGL <;> assumption)
