module

public import Formalism.LocalToGlobal.UnitaryNorms.CharExHost
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.CharExGen

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

namespace CharEx

def AlgValsFin (L : Type) [Field L] [NumberField L] : Prop :=
  ∀ (χ : HChar L) (s : ℝ) (m : (L →+* ℂ) → ℤ),
    (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) * ∏ φ : L →+* ℂ, ((‖φ (k : L)‖ : ℝ) : ℂ) ^ (s : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) →
    ∃ C : Subfield ℂ, FiniteDimensional ℚ C ∧ χ.ValuesIn s C.subtype

open Formalism.L2.Col

variable {X : Fields} (σ₀ : X.K →+* ℂ)


end CharEx

end Formalism.L2.Host
