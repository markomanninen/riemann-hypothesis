module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc UpperTheory.V.U3

section Gen

variable {Q A V V' : Type} [Field Q] [CommRing A] [Algebra Q A] [AddCommGroup V] [Module A V] [Module Q V]
  [IsScalarTower Q A V] [AddCommGroup V'] [Module A V'] [Module Q V'] [IsScalarTower Q A V']

private noncomputable def tr (B : Type) [AddCommGroup B] [Module Q B] (e : V ≃ₗ[A] V') :
    V ⊗[Q] B ≃ₗ[A] V' ⊗[Q] B := AlgebraTensorModule.congr e (LinearEquiv.refl Q B)

variable {B B' : Type} [AddCommGroup B] [Module Q B] [AddCommGroup B'] [Module Q B'] (e : V ≃ₗ[A] V')

private theorem tr_map {f : V →ₗ[A] V} {f' : V' →ₗ[A] V'} (h : ∀ x, e (f x) = f' (e x)) (b : B →ₗ[Q] B')
    (x : V ⊗[Q] B) :
    tr B' e (AlgebraTensorModule.map f b x) = AlgebraTensorModule.map f' b (tr B e x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [tr, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem tr_smul {K : Type} [AddCommGroup K] [Module Q K] (s : K →ₗ[Q] Module.End Q B) (c : A ⊗[Q] K)
    (x : V ⊗[Q] B) :
    tr B e (((TensorProduct.homTensorHomMap (RingHom.id Q) V B V B).comp
      (TensorProduct.map (Algebra.lsmul Q Q V : A →ₐ[Q] Module.End Q V).toLinearMap s)) c x) =
    ((TensorProduct.homTensorHomMap (RingHom.id Q) V' B V' B).comp
      (TensorProduct.map (Algebra.lsmul Q Q V' : A →ₐ[Q] Module.End Q V').toLinearMap s)) c (tr B e x) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c d hc hd => simp only [map_add (f := _), LinearMap.add_apply, hc, hd]
  | tmul a k =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simp [tr]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

end Gen

section Per

variable {l : ℕ} [Fact l.Prime] {A V V' : Type} [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V']
  [IsScalarTower ℚ_[l] A V'] (e : V ≃ₗ[A] V')

end Per
