module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationSqrtAbsNormEqOne

@[expose] public section

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_sqrt_absNorm_eq_one' : ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime → (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal → A.valuation (((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.valuation_sqrt_absNorm_eq_one | exact GlobalTheory.valuation_sqrt_absNorm_eq_one | (intros; apply GlobalTheory.valuation_sqrt_absNorm_eq_one <;> assumption)
