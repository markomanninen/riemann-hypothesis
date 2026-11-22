module

public import Mathlib
public import Formalism.HyperbolicPlaceProducts.Statement
public import Formalism.FlagUnipotentLattices.IdealCountLeW

@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField

namespace Formalism.HermitianLatticeCounting.S6

def EmbGen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (A : Submodule (𝓞 E) V) (Q : Type) [AddCommGroup Q]
    [Module (𝓞 E) Q] [Finite Q] (φ : Q →ₗ[𝓞 E] V ⧸ A), Function.Injective φ →
      ∃ s : Fin (Module.finrank E V) → Q, Submodule.span (𝓞 E) (Set.range s) = ⊤

end Formalism.HermitianLatticeCounting.S6
