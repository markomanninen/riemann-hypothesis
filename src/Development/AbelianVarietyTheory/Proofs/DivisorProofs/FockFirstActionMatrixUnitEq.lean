module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLineMatrixKroneckerRightFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueJointTop

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial GlobalTheory.Capelli GlobalTheory.Harm

namespace GlobalTheory.CompactHarm

variable {m k l : ℕ}

theorem omE_pp {p q r s : ℕ} (u v : Ln p q r s) (hu : linePos u = true) (hv : linePos v = true)
    (P : Pol p q r s) :
    omE u v P = X u * pderiv v P + (if u = v then (1 / 2 : ℂ) else 0) • P := by
  simp only [omE, raiB, lowB, hu, hv, if_true]
  split_ifs <;> simp

theorem omE_nn {p q r s : ℕ} (u v : Ln p q r s) (hu : linePos u = false) (hv : linePos v = false)
    (P : Pol p q r s) :
    omE u v P = -(X v * pderiv u P) - (if u = v then (1 / 2 : ℂ) else 0) • P := by
  have : omE u v P = -(pderiv u (X v * P)) + (if u = v then (1 / 2 : ℂ) else 0) • P := by
    simp only [omE, raiB, lowB, hu, hv, Bool.false_eq_true, if_false]
    split_ifs <;> simp
  rw [this, pderiv_X_mul']
  split_ifs
  · module
  · simp

end GlobalTheory.CompactHarm
