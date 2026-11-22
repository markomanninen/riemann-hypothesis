module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Objects

variable {K : Type*} [DecidableEq K] (ι : K → Type*) {F : Type*} [Field F]
variable {M : Type*} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M]


variable {ι}

end Objects

section Support

variable {S : Type*} [CommRing S] (M : Type*) [AddCommGroup M] [Module S M]

end Support

section Cycle

variable {K : Type*} [Fintype K] [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]
variable (M : Type*) [AddCommGroup M] [Module (MRing ι F) M]

end Cycle

section Statements

def HilbertIncrement.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (d : ℕ) (q : Ideal (MRing ι F)) (b : K) (i : ι b),
    IsMultiProjPrime q → ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    1 ≤ d → (X ⟨b, i⟩ : MRing ι F) ∉ q →
    (∀ a : K → ℤ, hilbFn q a - hilbFn q (a - Pi.single b 1) =
        hilbFn (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) a) ∧
    ∀ W : Ideal (MRing ι F), IsMultiProjPrime W → q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W →
      ringKrullDim (MRing ι F ⧸ W) ≤ ((d - 1 + Fintype.card K : ℕ) : WithBot ℕ∞)

end Statements

section Examples

variable {K : Type*} [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]

end Examples

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
