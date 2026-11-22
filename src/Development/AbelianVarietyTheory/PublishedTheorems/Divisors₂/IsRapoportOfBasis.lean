module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVHypSRetract
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLevelOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperRelAmpleOfSystem
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Elliptic

section

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

variable {A}

theorem cls_pull_lam {L : LB A.left} (hL : L.IsLB) {T : Over S} (x y : T ⟶ A)
    (h : ((abelian₂ A L).pull (lift x y).left).IsLB) : cls _ h = lam (cls L hL) x y := by
  rw [cls_pull (L := abelian₂ A L) (LB.isLB_linComb hL _ _) _ h]
  erw [cls_cube_two hL (fst A A) (snd A A)]
  rw [pull_lam, lift_fst, lift_snd]

end

variable {k : Type} [Field k] [IsAlgClosed k] (Q : Out.PolAV (Sp k)) (hg : Q.g = 1)

end GlobalTheory.RealMult.Elliptic

namespace GlobalTheory.RealMult

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]

end GlobalTheory.RealMult
