module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandTraceConjInvertibleScalarMatrix
public import Formalism.PeriodIntegrals.DSInfCharCap
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.RealPlaceAnalysis.StatementB

@[expose] public section

open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandTrace_conj_invertible_scalarMatrix : ∀ {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P → ∀ k : ℕ, Formalism.REAL.etr (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k = Formalism.REAL.etr E k := by
  first | exact @GlobalTheory.etr_conj_scalar_matrix | exact GlobalTheory.etr_conj_scalar_matrix | (intros; apply GlobalTheory.etr_conj_scalar_matrix <;> assumption)
