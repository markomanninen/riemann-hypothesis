module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteJumpsInfFiltration
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_setOf_inf_filtration_ne_succ : ∀ (E W : Type) [Field E] [AddCommGroup W] [Module E W] (D : Submodule E W) (F : ℤ → Submodule E W), Module.Finite E ↥D → (∀ a, F (a + 1) ≤ F a) → {a : ℤ | D ⊓ F (a + 1) ≠ D ⊓ F a}.Finite := by
  first | exact @GlobalTheory.finite_jumps_inf_filtration | exact GlobalTheory.finite_jumps_inf_filtration | (intros; apply GlobalTheory.finite_jumps_inf_filtration <;> assumption)
