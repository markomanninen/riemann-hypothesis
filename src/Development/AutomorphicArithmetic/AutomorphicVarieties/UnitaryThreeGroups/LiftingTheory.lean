module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.TypeIIrrCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem left_conj {R : Type} [CommRing R] {m : ℕ} (x y : GG (m := m) (R := R))
    (h1 : x.mat = 1) (h2 : x.right = -1) (h3 : y.right = 1) :
    (x * y * x⁻¹).left = theta y.left := by
  have hl : x.left = 1 := Units.ext h1
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
    hl, h2, h3, inv_one, mul_one, one_mul, sgnAct_neg_one, map_one]

private theorem pairing_theta {R : Type} [CommRing R] {m : ℕ} (a : GL (Fin m) R) :
    (a : Matrix (Fin m) (Fin m) R)ᵀ * Jmat R m * (theta a : GL (Fin m) R) = Jmat R m := by
  rw [theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat R m) (Jmat R m), Jmat_mul_Jmat,
    Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one,
    Matrix.one_mul]

private theorem cont_hom {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [Monoid M] [TopologicalSpace M]
    (f : Γ →* Mˣ) (h : Continuous fun g => (f g : M)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

private theorem irr_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) :
    (Af.tw ρ χ⁻¹).comp χ.ker.subtype = ρ.comp χ.ker.subtype := by
  refine MonoidHom.ext fun s => Units.ext ?_
  have hs : χ s = 1 := s.2
  show (Af.tw ρ χ⁻¹ s : Matrix (Fin n) (Fin n) k) = ρ s
  rw [Af.tw_val, MonoidHom.inv_apply, hs, inv_one, Units.val_one, one_smul]
