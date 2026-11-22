module

public import Mathlib
public import GroundTheory.AutomorphicForms.UnitaryGroupScheme

@[expose] public section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

variable {F E : Type*} [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ F E)

section Coordinates

variable (R : Type*) [CommRing R] [Algebra F R] {S : Type*} [CommRing S] [Algebra F S]

noncomputable def matrixCoords : Matrix ι ι (R ⊗[F] E) ≃ (ι × ι × κ → R) where
  toFun g p := (Algebra.TensorProduct.basis R b).repr (g p.1 p.2.1) p.2.2
  invFun x i j := (Algebra.TensorProduct.basis R b).repr.symm
    (Finsupp.equivFunOnFinite.symm fun k => x (i, j, k))
  left_inv g := by
    ext i j
    simp
  right_inv x := by
    funext ⟨i, j, k⟩
    simp

omit [Algebra.IsQuadraticExtension F E] [Fintype ι] [DecidableEq ι] in
theorem matrixCoords_apply (g : Matrix ι ι (R ⊗[F] E)) (i j : ι) (k : κ) :
    matrixCoords b R g (i, j, k) = (Algebra.TensorProduct.basis R b).repr (g i j) k := rfl


variable {R}


omit [Algebra.IsQuadraticExtension F E] [Fintype κ] in
theorem repr_tensorMap (f : R →ₐ[F] S) (z : R ⊗[F] E) (k : κ) :
    (Algebra.TensorProduct.basis S b).repr
        (TensorProduct.map f.toLinearMap (LinearMap.id : E →ₗ[F] E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]


omit [Algebra.IsQuadraticExtension F E] [Fintype ι] [DecidableEq ι] in
theorem matrixCoords_map (f : R →ₐ[F] S) (g : Matrix ι ι (R ⊗[F] E)) :
    matrixCoords b S (g.map (TensorProduct.map f.toLinearMap
      (LinearMap.id : E →ₗ[F] E))) =
      f ∘ matrixCoords b R g := by
  funext ⟨i, j, k⟩
  rw [Function.comp_apply, matrixCoords_apply, matrixCoords_apply, Matrix.map_apply, repr_tensorMap]

end Coordinates

end GroundTheory.Automorphic
