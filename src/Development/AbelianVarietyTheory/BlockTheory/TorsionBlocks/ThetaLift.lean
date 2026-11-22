module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataDIVDefs
public import Formalism.LocalRingCardinality.DataKap
public import Formalism.LocalRingCardinality.DataForms
public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions
open scoped Classical

namespace GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

section Theta
variable {P : Type} [Fintype P]

end Theta

section Schur
variable {T : Type} [Fintype T] {n₀ : ℕ}

end Schur

def hookProd (n : ℕ) (ν : ℕ → ℕ) : ℕ :=
  ∏ r ∈ Finset.range n, ∏ c ∈ Finset.range (ν r),
    ((ν r - c - 1) + ((Finset.Ioo r n).filter (fun r' => c < ν r')).card + 1)

variable (D : D7)

end GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices

end
