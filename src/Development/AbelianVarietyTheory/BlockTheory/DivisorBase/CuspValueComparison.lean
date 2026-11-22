module

public import Mathlib
public import Formalism.CyclotomicNorms.StatementT
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL

section OnePrime

variable {g : ℕ} [Fact g.Prime]

def rootC (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

def labelChar (ω : Fbar g →*₀ ℂ) (d : ℕ) (x y : Fbar g) : ℂ :=
  ω x ^ sInf {a : ℕ | ω y = rootC (g ^ d - 1) ^ a}


open Classical in
def cuspVal (ω : Fbar g →*₀ ℂ) (x : Fbar g) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod g)) : ℂ :=
  if ∃ (p : (ZMod g)[X]) (k : ℕ), Irreducible p ∧ M.charpoly = p ^ k then
    (-1) ^ (Fintype.card ι - 1) *
      ∑ y ∈ (rootsBar M.charpoly).toFinset, labelChar ω (Fintype.card ι) x y *
        ∏ i ∈ Finset.Ico 1 (Module.finrank (Fbar g)
            (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap (ZMod g) (Fbar g)))) y)),
          (1 - (g : ℂ) ^ ((rootsBar M.charpoly).toFinset.card * i))
  else 0

def IsTameLabel (ω : Fbar g →*₀ ℂ) (η : (ZMod g)ˣ → ℂ) (c : (ZMod g)ˣ) : Prop :=
  ∀ z : (ZMod g)ˣ, η z =
    labelChar ω 1 (algebraMap (ZMod g) (Fbar g) (c : ZMod g)) (algebraMap (ZMod g) (Fbar g) (z : ZMod g))

end OnePrime

section BothPrimes

variable {E : Type} [Field E] [NumberField E] [StarRing E] {gp : Fin 2 → ℕ} {pb : Fin 2 → 𝓞 E}

variable [∀ i, Fact (gp i).Prime] {K : Type} [Field K]

end BothPrimes

end GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison
