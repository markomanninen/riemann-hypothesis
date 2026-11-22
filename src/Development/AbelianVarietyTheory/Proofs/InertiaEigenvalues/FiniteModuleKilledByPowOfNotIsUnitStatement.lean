module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteModuleKilledByPowOfNotIsUnit
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete

@[expose] public section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_eq_zero_of_finite_of_not_isUnit : ∀ (O : Type) [CommRing O] [IsLocalRing O] (lam : O), ¬ IsUnit lam →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], ∃ a : ℕ, ∀ x : X, lam ^ a • x = 0 := by
  first | exact @GlobalTheory.finite_module_killed_by_pow_of_not_isUnit | exact GlobalTheory.finite_module_killed_by_pow_of_not_isUnit | (intros; apply GlobalTheory.finite_module_killed_by_pow_of_not_isUnit <;> assumption)
