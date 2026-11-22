module

public import Mathlib

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

abbrev Form (R : Type*) (n : ℕ) := Finset (Fin n) → R

def sg {n : ℕ} (I : Finset (Fin n)) (m : Fin n) : ℤ := (-1) ^ (I.filter fun j => m < j).card

variable {R : Type*} [CommRing R] {n : ℕ}

def oneF : Form R n := fun I => if I = ∅ then 1 else 0

def wedgeF (K : Form R n) (X : Fin n → R) : Form R n :=
  fun I => ∑ m ∈ I, ((sg I m : ℤ) : R) * K (I.erase m) * X m

def contrF (K : Form R n) (X : Fin n → R) : Form R n :=
  fun I => ∑ m ∈ Iᶜ, ((sg I m : ℤ) : R) * X m * K (insert m I)

def stepF (up : Bool) (K : Form R n) (X : Fin n → R) : Form R n :=
  if up then wedgeF K X else contrF K X

variable {ι : Type*}

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
