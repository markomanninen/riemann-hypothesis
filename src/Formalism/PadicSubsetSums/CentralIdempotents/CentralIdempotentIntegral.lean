module

public import Mathlib
public import Formalism.CyclotomicNorms.StatementTW

@[expose] public section

open Finset Polynomial Formalism.CyclotomicNorms

noncomputable section

namespace Formalism.IrreducibleCountingLemmas.TW

def CentralIdempotentIntegral : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G]
    (e : MonoidAlgebra K G), e * e = e → (∀ x : MonoidAlgebra K G, e * x = x * e) →
    ∀ g : G, IsIntegral ℤ ((Fintype.card G : K) * e.coeff g)

def relLen {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (M N : Submodule O V) : ℕ∞ :=
  Module.length O (↥M ⧸ N.comap M.subtype)

def sIdx {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (M N : Submodule O V) : ℤ :=
  ((relLen M N).toNat : ℤ) - ((relLen N M).toNat : ℤ)




end Formalism.IrreducibleCountingLemmas.TW
