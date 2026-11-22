module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace

open Matrix Formalism.UG ValuativeRel
open scoped TensorProduct
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsUWeilPair)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.LFun (HasSatU)

def str (q : ℂˣ) (n : ℤ) : Multiset ℂˣ := (Multiset.range n.toNat).map fun j : ℕ => q ^ (2 * (j : ℤ) - (n - 1))

section Valued

variable (E : Type) [Field E] [Valued E (WithZero (Multiplicative ℤ))]

def nu (z : Circle) : Eˣ →* Circle :=
  (zpowersHom Circle z⁻¹).comp ((WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).toMonoidHom.comp
    (Units.map (Valued.v : Valuation E (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom.toMonoidHom))

def chi (n : ℕ) : Eˣ →* Circle := nu E (Circle.exp Real.pi ^ n)

variable {E}

variable {n : ℕ}

def IsSelfDualLat (c : E →+* E) (S : Matrix (Fin n) (Fin n) E) (L : Submodule (intL E) (Fin n → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin n → E)) = ⊤ ∧
    ∀ x, x ∈ L ↔ ∀ y ∈ L, x ⬝ᵥ S *ᵥ (fun i => c (y i)) ∈ intL E

def IsHypFrame (c : E →+* E) (S : Matrix (Fin n) (Fin n) E) (L : Submodule (intL E) (Fin n → E)) (P : GL (Fin n) E) :
    Prop :=
  (∀ y : Fin n → E, P.1 *ᵥ y ∈ L ↔ ∀ i, y i ∈ intL E) ∧
    ∃ u : E, Valued.v u = 1 ∧ P.1ᵀ * S * P.1.map c = u • antiJ E n

end Valued

section Local

variable {F : Type} [Field F] {E : Type} [Field E] [Valued E (WithZero (Multiplicative ℤ))] [Algebra F E]
  (c : E →ₐ[F] E) {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]

end Local

section Res

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]


variable {F} in
def IsUnramAdd (ϖ : F) (ψ : AddChar F ℂ) : Prop :=
  (∀ x ∈ 𝒪[F], ψ x = 1) ∧ ∃ x ∈ 𝒪[F], ψ (ϖ⁻¹ * x) ≠ 1

end Res

end GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace

end
