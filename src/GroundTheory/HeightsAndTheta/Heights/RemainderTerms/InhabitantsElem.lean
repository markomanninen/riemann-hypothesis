module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsElem
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Inhabitants
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Elementary

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

theorem flagIntegral_C_mul (f N : ℕ) (b : ℚ) (Φ : RootRing f N) :
    flagIntegral f N (C b * Φ) = b * flagIntegral f N Φ := by
  simp only [flagIntegral, coeff_C_mul, Finset.mul_sum, mul_assoc]

end

end RestTerms

end GroundTheory.Heights₂.Heights
