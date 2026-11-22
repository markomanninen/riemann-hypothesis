module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps

@[expose] public section

noncomputable section

open WittVector Ideal Matrix GlobalTheory.Sandwich TensorProduct

namespace GlobalTheory.DetInv

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

variable (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ]

variable {p O Λ}

abbrev rhoTA {ε : PreTilt O p} {h : ℕ} (D : Datum ε h Λ) (l : Λ) :
    Matrix (Fin h) (Fin h) (Ainf p O) := (D.ρT l).map (ofPadic p O)

end GlobalTheory.DetInv
