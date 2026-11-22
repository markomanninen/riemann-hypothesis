module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut

@[expose] public section

noncomputable section

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

namespace GlobalTheory.GamMul

section Blocks

variable {R : Type} [CommRing R]


open Classical in
def toGL {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : GL (Fin n) R := if h : IsUnit M then h.unit else 1

end Blocks

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (p q : ℕ) (c : kˣ) : Set (Matrix (Fin p) (Fin q) k) := {X | ∀ i j, valuation k (X i j) ≤ valuation k (c : k)}

end GlobalTheory.GamMul

end
