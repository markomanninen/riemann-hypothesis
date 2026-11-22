module

public import Mathlib

@[expose] public section

namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

variable {O R K : Type*} [CommRing O] [CommRing R] [CommRing K] [Algebra O R] [Algebra O K]

def Sep (Y : Set (R →ₐ[O] K)) : Prop := ∀ f : R, (∀ y ∈ Y, y f = 0) → f = 0

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
