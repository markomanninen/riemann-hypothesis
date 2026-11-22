module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfFunctionProductSumsEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multilinear_sum_eq_of_function_product_sums_eq : ∀ {ι κ Δ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {X : ι → Type} {Y : κ → Type}
    {V : ∀ i, Submodule ℂ (X i → ℂ)} {V' : ∀ j, Submodule ℂ (Y j → ℂ)}
    (M : MultilinearMap (RingHom.id ℂ) (fun i => V i)
      (MultilinearMap (RingHom.id ℂ) (fun j => V' j) ℂ)) (τ : Δ →₀ ℂ)
    (f f' : Δ → ∀ i, V i) (g g' : Δ → ∀ j, V' j),
    (∀ (x : ∀ i, X i) (y : ∀ j, Y j),
      (τ.sum fun d a => a * (∏ i, (f d i : X i → ℂ) (x i)) * ∏ j, (g d j : Y j → ℂ) (y j)) =
        τ.sum fun d a => a * (∏ i, (f' d i : X i → ℂ) (x i)) * ∏ j, (g' d j : Y j → ℂ) (y j)) →
    (τ.sum fun d a => a * M (f d) (g d)) = τ.sum fun d a => a * M (f' d) (g' d) := by
  exact @GlobalTheory.funProd_multilinear_sum_eq
