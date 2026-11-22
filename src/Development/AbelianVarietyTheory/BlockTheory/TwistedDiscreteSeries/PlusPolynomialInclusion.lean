module

public import Mathlib
public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

noncomputable section

open Polynomial TensorProduct Matrix NumberField IsDedekindDomain Formalism.UG

namespace GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def sharp (c : E ≃ₐ[F] E) (r : ℕ) (P : E[X]) : E[X] :=
  C (c (P.coeff 0))⁻¹ * reflect r (P.map (c : E →+* E))

def IsPPol (c : E ≃ₐ[F] E) (r : ℕ) (P : E[X]) : Prop :=
  P.Monic ∧ Irreducible P ∧ P.natDegree = r ∧ P.coeff 0 ≠ 0 ∧ P = sharp c r P

variable {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}

theorem isUnit_root (hP : IsPPol c r P) : IsUnit (AdjoinRoot.root P) := by
  haveI : Fact (Irreducible P) := ⟨hP.2.1⟩
  refine Ne.isUnit fun h => hP.2.2.2.1 ?_
  have h1 := AdjoinRoot.eval₂_root P
  rw [h, eval₂_at_zero] at h1
  exact (map_eq_zero_iff _ (AdjoinRoot.of P).injective).1 h1

def alpha (hP : IsPPol c r P) : (AdjoinRoot P)ˣ := (isUnit_root hP).unit

theorem eval₂_conj_inv (hP : IsPPol c r P) :
    P.eval₂ ((AdjoinRoot.of P).comp (c : E →+* E)) ((alpha hP)⁻¹ : (AdjoinRoot P)ˣ) = 0 := by
  rw [← eval₂_map]
  letI : Invertible (((alpha hP)⁻¹ : (AdjoinRoot P)ˣ) : AdjoinRoot P) := Units.invertible _
  have hd : (P.map (c : E →+* E)).natDegree ≤ r := hP.2.2.1 ▸ natDegree_map_le
  rw [← eval₂_reflect_eq_zero_iff _ _ r _ hd]
  have h1 : ⅟(((alpha hP)⁻¹ : (AdjoinRoot P)ˣ) : AdjoinRoot P) = AdjoinRoot.root P := rfl
  have h2 : reflect r (P.map (c : E →+* E)) = C (c (P.coeff 0)) * P := by
    have hne : c (P.coeff 0) ≠ 0 := by simpa using hP.2.2.2.1
    conv_rhs => rw [hP.2.2.2.2]
    rw [← hP.2.2.2.2]
    conv_rhs => arg 2; rw [hP.2.2.2.2]
    rw [sharp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hne, C_1, one_mul]
  rw [h1, h2, eval₂_mul, AdjoinRoot.eval₂_root, mul_zero]

def starL (hP : IsPPol c r P) : AdjoinRoot P →ₐ[F] AdjoinRoot P :=
  { AdjoinRoot.lift ((AdjoinRoot.of P).comp (c : E →+* E))
      (((alpha hP)⁻¹ : (AdjoinRoot P)ˣ) : AdjoinRoot P) (eval₂_conj_inv hP) with
    commutes' := fun a => by
      have h : algebraMap F (AdjoinRoot P) a = AdjoinRoot.of P (algebraMap F E a) := rfl
      rw [h]
      simp }

def Lplus (hP : IsPPol c r P) : Subalgebra F (AdjoinRoot P) :=
  AlgHom.equalizer (starL hP) (AlgHom.id F (AdjoinRoot P))

variable (k : Type) [Field k] [Algebra F k]

@[reducible] def algLk (P : E[X]) : Algebra (E ⊗[F] k) (AdjoinRoot P ⊗[F] k) :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom F E (AdjoinRoot P))
    (AlgHom.id F k)).toRingHom.toAlgebra

attribute [local instance] algLk

def starLk (hP : IsPPol c r P) : AdjoinRoot P ⊗[F] k →+* AdjoinRoot P ⊗[F] k :=
  sigR (starL hP) k

def inclPlus (hP : IsPPol c r P) : Lplus hP ⊗[F] k →+* AdjoinRoot P ⊗[F] k :=
  (Algebra.TensorProduct.map (Lplus hP).val (AlgHom.id F k)).toRingHom

def trLk (P : E[X]) : AdjoinRoot P ⊗[F] k →ₗ[F] E ⊗[F] k :=
  TensorProduct.map ((Algebra.trace E (AdjoinRoot P)).restrictScalars F) LinearMap.id

def hx (hP : IsPPol c r P) (x : (Lplus hP ⊗[F] k)ˣ) (y y' : AdjoinRoot P ⊗[F] k) : E ⊗[F] k :=
  trLk k P (inclPlus k hP x * y * starLk k hP y')

variable {k}

variable (k)

end GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
