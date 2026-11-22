module

public import Mathlib
public import Formalism.DegreeFormula.FlagDegFormula

@[expose] public section

open MvPolynomial Formalism.DegreeFormula

noncomputable section

namespace GlobalTheory.FlagPoly

abbrev Pol (ι : Type) (N : ℕ) : Type := MvPolynomial (ι × Fin N) ℝ

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

def pLow (j : ℕ) (τ : ι) (k : ℕ) : Pol ι N :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), X (τ, i) ^ k

def pHigh (j : ℕ) (τ : ι) (k : ℕ) : Pol ι N :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ)), X (τ, i) ^ k

def ev (lam : ι → Fin N → ℝ) (P : Pol ι N) : ℝ := eval (fun x => lam x.1 x.2) P

def lamA (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N := ∑ τ : ι, (pHigh j τ 1 - pLow j τ 1)

def fibPt (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N :=
  ∏ x : ι × Fin N, (-X x) ^ (if (x.2 : ℕ) < j then j - 1 - (x.2 : ℕ) else N - 1 - (x.2 : ℕ))

def dimGr (ι : Type) [Fintype ι] (N j : ℕ) : ℕ := Fintype.card ι * (j * (N - j))

def curveCl (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N := lamA ι N j ^ (dimGr ι N j - 1) * fibPt ι N j

end GlobalTheory.FlagPoly
