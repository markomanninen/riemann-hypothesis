module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LangXRoot

@[expose] public section

open GlobalTheory.Col PowerSeries

namespace GlobalTheory.LangWitt

open Matrix

section Field

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

end Field

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p]

variable [IsAlgClosed k]

theorem map_add' {R S : Type} [Ring R] [Ring S] (f : R →+* S) {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) R) : (A + B).map f = A.map f + B.map f :=
  map_add f.mapMatrix A B

end Witt

end GlobalTheory.LangWitt
