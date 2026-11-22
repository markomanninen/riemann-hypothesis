module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieInh

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem stdSmooth_mvPolynomial (R : Type) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  have hker : (Algebra.Generators.mvPolynomial R (Fin n)).ker = ⊥ := by
    rw [Algebra.Generators.ker_eq_ker_aeval_val, Algebra.Generators.mvPolynomial_val]
    exact (RingHom.injective_iff_ker_eq_bot _).1 fun a b h => by
      simpa only [MvPolynomial.aeval_X_left_apply] using h
  let P : Algebra.Presentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    ⟨Algebra.Generators.mvPolynomial R (Fin n), Empty.elim, by rw [hker]; simp⟩
  let P' : Algebra.PreSubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    ⟨P, Empty.elim, fun a => a.elim⟩
  let P'' : Algebra.SubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    ⟨P', by
      rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_isEmpty, map_one]
      exact isUnit_one⟩
  refine Algebra.IsStandardSmoothOfRelativeDimension.mk ⟨Fin n, Empty, inferInstance, inferInstance, P'', ?_⟩
  simp [Algebra.Presentation.dimension]

variable {X : Scheme.{0}}

variable {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ X)

end GlobalTheory.CompanionTheory.Ar.LieInh

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

end GlobalTheory.CompanionTheory.Ar
