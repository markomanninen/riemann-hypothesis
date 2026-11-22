module

public import Mathlib
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.HarderNarasimhan.QuotRealize

@[expose] public section

open Module NumberField

noncomputable section

namespace Formalism.DivisionValues

def DualMu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (D : ℕ), 0 < D →
    ∀ X : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsFullLattice K R →
      Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame X) (Formalism.HN.dualLat R) =
        lcv X R / D

end Formalism.DivisionValues
