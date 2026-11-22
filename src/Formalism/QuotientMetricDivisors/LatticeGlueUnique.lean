module

public import Mathlib
public import Formalism.QuotientMetricDivisors.Statement

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

def glueLat {K : Type} [Field K] [NumberField K] {D : ℕ}
    (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K)) : Submodule (𝓞 K) (Fin D → K) :=
  ⨅ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w)

def LatticeGlue : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : ℕ) (L0 : Submodule (𝓞 K) (Fin D → K))
    (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K)),
    Submodule.IsFullLattice K L0 → (∀ w, Submodule.IsFullLattice K (L w)) →
    {w : HeightOneSpectrum (𝓞 K) |
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w) ≠ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L0}.Finite →
    Submodule.IsFullLattice K (glueLat L) ∧
      ∀ w : HeightOneSpectrum (𝓞 K),
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (glueLat L) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w)

end Formalism.DivisionValues
