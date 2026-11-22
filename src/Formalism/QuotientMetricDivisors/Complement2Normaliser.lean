module

public import Mathlib
public import Formalism.QuotientMetricDivisors.ProdFormula
public import Formalism.LogFactorialIndices.StatementSize

@[expose] public section

open Module NumberField IsDedekindDomain Finset

noncomputable section

namespace Formalism.DivisionValues

def PlOver {K : Type} [Field K] [NumberField K] (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) : Prop :=
  0 < vw w (g : K)

def PlOverCoprime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g g' : ℕ), Nat.Coprime g g' →
    ∀ w : HeightOneSpectrum (𝓞 K), ¬ (PlOver g w ∧ PlOver g' w)

end Formalism.DivisionValues
