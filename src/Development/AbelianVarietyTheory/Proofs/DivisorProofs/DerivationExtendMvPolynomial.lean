module

public import Mathlib

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory


open MvPolynomial in
noncomputable def coeffDerivFun {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p : MvPolynomial τ B) : MvPolynomial τ B :=
  ∑ s ∈ p.support, MvPolynomial.monomial s (D (p.coeff s))

open MvPolynomial in
theorem coeff_coeffDerivFun {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p : MvPolynomial τ B) (m : τ →₀ ℕ) :
    (coeffDerivFun D p).coeff m = D (p.coeff m) := by
  classical
  rw [coeffDerivFun, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

noncomputable def coeffDerivAddHom {B τ : Type} [CommRing B] (D : Derivation ℤ B B) :
    MvPolynomial τ B →+ MvPolynomial τ B where
  toFun := coeffDerivFun D
  map_zero' := by ext m; simp [coeff_coeffDerivFun]
  map_add' p q := by ext m; simp [coeff_coeffDerivFun]

theorem coeffDerivAddHom_monomial {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (s : τ →₀ ℕ) (a : B) :
    coeffDerivAddHom D (MvPolynomial.monomial s a) = MvPolynomial.monomial s (D a) := by
  classical
  ext m
  change AddMonoidAlgebra.coeff (coeffDerivFun D _) m = _
  rw [coeff_coeffDerivFun, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  split_ifs <;> simp

theorem coeffDerivAddHom_mul {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p q : MvPolynomial τ B) :
    coeffDerivAddHom D (p * q) = p * coeffDerivAddHom D q + q * coeffDerivAddHom D p := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    induction q using MvPolynomial.induction_on' with
    | monomial v b =>
      simp only [MvPolynomial.monomial_mul_monomial, coeffDerivAddHom_monomial, Derivation.leibniz,
        smul_eq_mul, map_add, add_comm v u]
    | add q₁ q₂ h₁ h₂ =>
      rw [mul_add, map_add (f := _), h₁, h₂, map_add (f := _)]; ring
  | add p₁ p₂ h₁ h₂ =>
    rw [add_mul, map_add (f := _), h₁, h₂, map_add (f := _)]; ring

theorem derivation_extend_mvPolynomial :
    ∀ (B τ : Type) [CommRing B] (D : Derivation ℤ B B),
      ∃ D' : Derivation ℤ (MvPolynomial τ B) (MvPolynomial τ B),
        (∀ x, D' (MvPolynomial.C x) = MvPolynomial.C (D x)) ∧ ∀ t, D' (MvPolynomial.X t) = 0 := by
  intro B τ _ D
  refine ⟨Derivation.mk' (coeffDerivAddHom D).toIntLinearMap
    (fun a b => by simpa [smul_eq_mul] using coeffDerivAddHom_mul D a b), ?_, ?_⟩
  · intro x
    show coeffDerivAddHom D (MvPolynomial.monomial 0 x) = MvPolynomial.monomial 0 (D x)
    exact coeffDerivAddHom_monomial D 0 x
  · intro t
    show coeffDerivAddHom D (MvPolynomial.monomial (Finsupp.single t 1) 1) = 0
    rw [coeffDerivAddHom_monomial, Derivation.map_one_eq_zero, map_zero]

end GlobalTheory
