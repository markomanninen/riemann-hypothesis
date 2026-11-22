module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerPowEqOfFrobeniusRatio
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_pow_eq_of_frobenius_ratio : ∀ (l : ℕ) [Fact l.Prime] (w' : Formalism.Per.Acris l) (ζ : Formalism.Per.Fl l), w' ≠ 0 → φc l (tc l ζ * w') * w' = tc l ζ * w' * φc l w' → ζ ^ l = ζ := by
  first | exact @GlobalTheory.PMon.Gauss.teich_eq_of_phi_ratio | exact GlobalTheory.PMon.Gauss.teich_eq_of_phi_ratio | (intros; apply GlobalTheory.PMon.Gauss.teich_eq_of_phi_ratio <;> assumption)
