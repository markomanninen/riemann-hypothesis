module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero

@[expose] public section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.GradR

theorem detR_isHomogeneous (P Q R : ℕ) (h : P ≤ R) : (detR P Q R h).IsHomogeneous P := by
  unfold detR
  rw [Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have h1 : (∏ i : Fin P, (Matrix.of fun a c : Fin P =>
      (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)) (σ i) i).IsHomogeneous (∑ _i : Fin P, 1) :=
    IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X ℂ _
  have h0 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Pol P Q R 0).IsHomogeneous 0 := by
    have := isHomogeneous_C (Ix P Q × Ix R 0) (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)
    rwa [map_intCast] at this
  simpa using h0.mul h1

end GlobalTheory.CharPair.GradR
