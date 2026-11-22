module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.CovarianceFormula

@[expose] public section

open scoped Classical ENNReal
open MeasureTheory

noncomputable section

namespace GlobalTheory.CovNFormulaPf

theorem pi_const_smul' {ι : Type} [Fintype ι] {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (c : NNReal) :
    Measure.pi (fun _ : ι => c • μ) = (c ^ Fintype.card ι) • Measure.pi (fun _ : ι => μ) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi]
  simp only [Measure.coe_nnreal_smul_apply, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ENNReal.coe_pow]

theorem main : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula :=
  Formalism.MainStatements.RowRest.covariance_formula

end GlobalTheory.CovNFormulaPf
