module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteBreuilKisinQuotientPrimePowXPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_breuilKisin_quotient_prime_pow_X_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n c : ℕ), Finite (bk.S ⧸ (Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {(X : bk.S) ^ c})) := by
  first | exact @GlobalTheory.BKFin.finite_quot | exact GlobalTheory.BKFin.finite_quot | (intros; apply GlobalTheory.BKFin.finite_quot <;> assumption)
