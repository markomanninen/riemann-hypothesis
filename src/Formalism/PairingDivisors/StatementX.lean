module

public import Mathlib
public import Formalism.PairingDivisors.StatementH

@[expose] public section

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)

noncomputable section

namespace Formalism.PairingDivisionLocalBalance

def HtLe {K : Type} [Field K] [NumberField K] [StarRing K] (g : Pl K → ℤ) (z : K) (B : ℝ) : Prop :=
  (Function.support fun w : Pl K => lw w * |((vw w z + g w : ℤ) : ℝ)|).Finite ∧
  ∑ᶠ w : Pl K, lw w * |((vw w z + g w : ℤ) : ℝ)| ≤ B

end Formalism.PairingDivisionLocalBalance
