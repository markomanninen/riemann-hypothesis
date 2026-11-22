module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfMuFrobeniusEquationSolvableAndTendsto
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_mu_frobenius_equation_solvable_and_tendsto : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), (∀ q : Ainf l, ∃ y : Ainf l, AI.μ * y - WittVector.frobenius (AI.μ * y) = AI.μ * q) ∧ ∀ M n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, (WittVector.frobenius : Ainf l →+* Ainf l)^[k] AI.μ ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M} := by
  first | exact @GlobalTheory.ExpImage.Conv.main | exact GlobalTheory.ExpImage.Conv.main | (intros; apply GlobalTheory.ExpImage.Conv.main <;> assumption)
