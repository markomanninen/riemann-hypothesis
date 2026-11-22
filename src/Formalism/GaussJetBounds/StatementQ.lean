module

public import Formalism.GaussJetBounds.StatementN

@[expose] public section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

def IntOp : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type) (Th : MvPowerSeries ι K),
    JetsIntegral Th → ∀ P : MvPolynomial ι K, (∀ n, ‖AddMonoidAlgebra.coeff P n‖ ≤ 1) →
      ‖jetPair P Th‖ ≤ 1

end Formalism.DworkPowerSeriesWeights
