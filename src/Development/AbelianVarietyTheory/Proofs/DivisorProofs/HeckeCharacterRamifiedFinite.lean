module

public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.HCharRam

theorem ram_finite : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K),
    {w : HeightOneSpectrum (𝓞 K) | ¬ χ.UnrAt w}.Finite := by
  intro K _ _ χ
  exact Filter.eventually_cofinite.1 (GlobalTheory.HeckeSplit.eventually_unrAt χ.1 χ.2.1)

end GlobalTheory.HCharRam
