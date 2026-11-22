module

public import Mathlib

@[expose] public section

open Real Finset

namespace Formalism.RankGapBounds.ChebyshevFactorialBounds

noncomputable section

def primesUpTo (X : ℕ) : Finset ℕ := (Finset.range (X + 1)).filter Nat.Prime

structure Data (ι : Type) where

  T2 : Finset ι

  Nr : ℕ
  k : ℕ
  t : ℕ
  m : ℕ
  h : ℕ
  S : ℕ
  eta' : ℕ
  Wthin : ℕ
  D0 : ℕ
  lJ : ℝ
  Kexc : ℝ
  q : ι → ℕ
  j : ι → ℕ
  xlo : ι → ℤ
  xhi : ι → ℤ
  maxB : ι → ℤ
  Exc : Finset ℕ
  Bad : Finset ℕ
  J : ℕ → ℕ
  ex : ι → ℕ → ℕ
  ecl : ι → ℕ → ℕ
  erest : ι → ℕ → ℕ
  mw : ι → ℕ → ℕ
  mwF : ι → ℕ → ℕ

namespace Data

end Data

def ChebyshevTheta : Prop :=
  ∀ n : ℕ, ∑ p ∈ primesUpTo n, Real.log (p : ℝ) ≤ Real.log 4 * (n : ℝ)

end

end Formalism.RankGapBounds.ChebyshevFactorialBounds
