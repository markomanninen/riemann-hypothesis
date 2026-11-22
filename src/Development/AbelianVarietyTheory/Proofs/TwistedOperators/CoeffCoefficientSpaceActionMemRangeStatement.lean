module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffCoefficientSpaceActionMemRange
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReprMemOfCoeff

@[expose] public section

open Formalism.L2.DIV MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_coefficientSpaceAction_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} {E : Type} [Field E] (emb : ι → E →+* ℂ) {L : Type} [Field L] (κ : L →+* ℂ), (∀ (τ : ι) (x : E), emb τ x ∈ Set.range κ) → ∀ (lam : ι → Formalism.BasicNotions.DomWeight n) (g : GL (Fin n) E) (v : VV ℂ lam), (∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) → ∀ m, AddMonoidAlgebra.coeff ((rhoVr emb lam g) v).1 m ∈ Set.range κ := by
  first | exact @GlobalTheory.RowRho.coeff_rhoVr_mem_range | exact GlobalTheory.RowRho.coeff_rhoVr_mem_range | (intros; apply GlobalTheory.RowRho.coeff_rhoVr_mem_range <;> assumption)
