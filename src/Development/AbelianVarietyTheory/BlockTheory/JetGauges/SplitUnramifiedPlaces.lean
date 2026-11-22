module

public import Mathlib

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

section Ring

variable (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]

abbrev Op : Type := ℤ_[p] ⊗[ℤ] OE

def bar [StarRing OE] : Op p OE ≃ₐ[ℤ_[p]] Op p OE :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p])
    (AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut OE)) (fun n => by simp))

variable {p OE}

def extend {O : Type} [CommRing O] [Algebra ℤ_[p] O] (σ : OE →+* O) : Op p OE →ₐ[ℤ_[p]] O :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[p] O) σ.toIntAlgHom (fun _ _ => Commute.all _ _)

end Ring

@[ext] structure Place (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] where

  e : Op p OE
  idem : IsIdempotentElem e
  ne_zero : e ≠ 0
  primitive : ∀ f : Op p OE, IsIdempotentElem f → f * e = f → f = 0 ∨ f = e

namespace Place

variable {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE]

abbrev Ow (w : Place p OE) : Type := Op p OE ⧸ Ideal.span {1 - w.e}

def toOw (w : Place p OE) : OE →+* w.Ow :=
  (Ideal.Quotient.mk _).comp
    (Algebra.TensorProduct.includeRight : OE →ₐ[ℤ] Op p OE).toRingHom

end Place

section Gauss

variable {p : ℕ} [Fact p.Prime]

end Gauss

end GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
