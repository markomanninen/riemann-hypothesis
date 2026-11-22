module

public import Formalism.GaloisIrreducibility.Statement

@[expose] public section

namespace Formalism.GaloisIrreducibility
open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R]

@[simp] lemma zero_ne_succ' {m : ℕ} (k : Fin m) : ((0 : Fin (m+1)) = k.succ) ↔ False := ⟨fun h => Fin.succ_ne_zero k h.symm, fun h => h.elim⟩

end BorderedIndexCases

open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R]

end BorderedIndexCases

open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R] [IsLocalRing R]

end BorderedIndexCases

end Formalism.GaloisIrreducibility
