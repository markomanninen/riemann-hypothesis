module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationXiZeroEqOne

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

theorem sum_fin_two_mul_add_one {M : Type*} [AddCommMonoid M] {ρ n : ℕ} (hn : n = 2 * ρ + 1) (f : Fin n → M)
    (a b : Fin ρ → M) (m : M) (ha : ∀ (i : Fin ρ) (j : Fin n), j.1 = i.1 → f j = a i) (hm : ∀ j : Fin n, j.1 = ρ → f j = m)
    (hb : ∀ (i : Fin ρ) (j : Fin n), j.1 + i.1 = 2 * ρ → f j = b i) :
    ∑ j, f j = ∑ i, a i + m + ∑ i, b i := by
  subst hn
  have e : ρ + (1 + ρ) = 2 * ρ + 1 := by omega
  rw [← Fin.sum_congr' f e, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one, add_assoc]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => ha i _ (by simp)
  · congr 1
    · exact hm _ (by simp)
    · rw [← Equiv.sum_comp Fin.revPerm b]
      refine Finset.sum_congr rfl fun i _ => hb _ _ ?_
      simp [Fin.val_rev]
      omega

theorem mul_div_mem_integer_iff {k : Type} [Field k] [ValuativeRel k] {c : k} (hc : valuation k c = 1) (w z : k) :
    w * (z / c) ∈ 𝒪[k] ↔ w * z ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, map_mul, map_mul, map_div₀, hc, div_one]

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem mul_mul_div_cancel_left' {k : Type} [Field k] {c : k} (hc : c ≠ 0) (P X : k) : c * P * (X / c) = P * X := by
  field_simp

end GlobalTheory.Core.Mi.LatMatch

end
