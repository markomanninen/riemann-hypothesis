module

public import Mathlib
public import Formalism.HermitianLattices.StatementTheta
public import Formalism.HermitianLattices.GenusCovolBound

@[expose] public section

open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Defs

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V]

abbrev discr (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) : Type _ :=
  (tdualSub h L) ⧸ (L.comap (tdualSub h L).subtype)

variable [IsScalarTower (NumberField.RingOfIntegers K) K V]

end Defs

end Formalism.HermitianLatticesTheory
