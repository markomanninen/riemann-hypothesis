module

public import Formalism.QuotientMetricDivisors.ProdFormula
public import Mathlib
public import Formalism.QuotientMetricDivisors.StatementJ
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.BoundsSum

@[expose] public section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

theorem lw_nonneg' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    0 ≤ lw w := by
  unfold lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

end Formalism.DivisionValues
