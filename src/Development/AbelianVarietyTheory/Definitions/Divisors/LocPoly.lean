module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import GroundTheory.AutomorphicForms.ReductionSplitting
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaPair

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Polynomial GroundTheory.Automorphic UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf toL rmul invSet CuspSub)
open scoped ContDiff

namespace GlobalTheory.HenQ

section Fin

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

end Fin

section Inf

variable {K : Type} [Field K] [NumberField K] {n : ℕ}


open Classical in
def pdL (v : InfinitePlace K) (i j : Fin n) (F : Lie K n → ℂ) (x : Lie K n) : ℂ :=
  fderiv ℝ F x (toL (Matrix.single i j (Pi.single v 1)))


def detD (v : InfinitePlace K) (F : Lie K n → ℂ) (x : Lie K n) : ℂ :=
  ∑ p : Equiv.Perm (Fin n), (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℂ) * (List.finRange n).foldr (fun j G => pdL v (p j) j G) F x

def IsTest (Φ : Lie K n → ℂ) : Prop := ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ invSet K n

variable [IsTotallyReal K]

end Inf

end GlobalTheory.HenQ
