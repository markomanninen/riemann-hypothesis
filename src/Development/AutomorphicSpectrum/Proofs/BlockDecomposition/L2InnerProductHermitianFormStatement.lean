module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerProductHermitianForm

@[expose] public section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.l2_inner_product_hermitian_form : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsOpenPosMeasure], (∀ x y : GlobalTheory.CompanionTheory.ModelS.SmF n, conj (GlobalTheory.CompanionTheory.ModelS.ipK κ y x) = GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ (∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, 0 ≤ (GlobalTheory.CompanionTheory.ModelS.ipK κ x x).re) ∧ (∀ x y z : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ (x + y) z = GlobalTheory.CompanionTheory.ModelS.ipK κ x z + GlobalTheory.CompanionTheory.ModelS.ipK κ y z) ∧ (∀ (c : ℂ) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (c • x) y = conj c * GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ ∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ x x = 0 → ∀ k : Matrix.unitaryGroup (Fin n) ℂ, x.1 k.1 = 0 :=
  @GlobalTheory.CompanionTheory.ModelS.L2InnerProduct.ipK_form
