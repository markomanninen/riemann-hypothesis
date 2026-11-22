module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffEqTensorSquareTopCoefficient
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecMulVecComm

@[expose] public section

open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_eq_tensorSquareTopCoefficient : ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ), GlobalTheory.GoodMetric.topCoeff P = GlobalTheory.GrassModel.topBig n (GlobalTheory.GrassModel.toEven n P : GlobalTheory.GrassModel.Big n) := by
  first | exact @GlobalTheory.GrassModel.TopRead.topCoeff_eq_topBig | exact GlobalTheory.GrassModel.TopRead.topCoeff_eq_topBig | (intros; apply GlobalTheory.GrassModel.TopRead.topCoeff_eq_topBig <;> assumption)
