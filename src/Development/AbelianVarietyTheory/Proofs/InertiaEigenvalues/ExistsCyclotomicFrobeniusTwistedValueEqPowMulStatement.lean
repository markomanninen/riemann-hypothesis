module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEqPowMul
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq_pow_mul : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ), 1 ≤ s → ∀ α : Om l, α ∈ Ks K s → ‖α‖ ≤ 1 → ∃ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) ∧ ‖(d : Om l)‖ ≤ 1 ∧ d - (l : ↥(K0 K)) ^ e * frK P K d = (frK P K ^ s) (∑ a ∈ primeTo l s, lam a) ∧ cycVal P K s e lam d = (l : Om l) ^ ((e + 1) * (s - 1)) * α := by
  first | exact @GlobalTheory.ExpImage.exists_cycVal_eq_pow_mul | exact GlobalTheory.ExpImage.exists_cycVal_eq_pow_mul | (intros; apply GlobalTheory.ExpImage.exists_cycVal_eq_pow_mul <;> assumption)
