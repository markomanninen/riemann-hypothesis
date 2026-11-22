module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

@[expose] public section

noncomputable section
namespace GlobalTheory.FockAlg.Model
open Formalism.BasicNotions.TH MvPolynomial

def fockEmb (σ : Type) [DecidableEq σ] :
    MvPolynomial σ ℂ →ₗ[ℂ] lp (fun _ : σ →₀ ℕ => ℂ) 2 :=
  (basisMonomials σ ℂ).constr ℂ fun α =>
    lp.single 2 α ((Real.sqrt (α.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ)

theorem isFockIsometry_fockEmb (σ : Type) [DecidableEq σ] : IsFockIP (fockEmb σ) := by
  intro α β
  have h : ∀ γ : σ →₀ ℕ, fockEmb σ (monomial γ 1) =
      lp.single 2 γ ((Real.sqrt (γ.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ) := by
    intro γ
    have := (basisMonomials σ ℂ).constr_basis ℂ (fun α : σ →₀ ℕ =>
      (lp.single 2 α ((Real.sqrt (α.prod fun _ k => (k.factorial : ℝ)) : ℝ) : ℂ) :
        lp (fun _ : σ →₀ ℕ => ℂ) 2)) γ
    simpa [fockEmb] using this
  rw [h, h, lp.inner_single_left]
  split_ifs with e
  · subst e
    have h0 : 0 ≤ α.prod fun _ k => (k.factorial : ℝ) :=
      Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    rw [lp.single_apply_self, RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt h0]
    simp [Finsupp.prod]
  · rw [lp.single_apply_ne _ _ _ e, inner_zero_right]

end GlobalTheory.FockAlg.Model
