module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def kernSum (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (f : ∀ w : Pl E, UL n w → ℂ) : ℂ :=
  (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ *
    ∑ᶠ q : DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n))),
      ((Nat.card (ratFinU E n ⊓ (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU (E := E) (n := n))) :
        ℂ))⁻¹ *
      ∑ᶠ γ : UE E n, globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q) * chW lam γ.1.val.charpoly

def clsSum (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) (γ : UE E n) : ℂ :=
  (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ *
    ∑ᶠ q : DoubleCoset.Quotient ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt γ) : Subgroup (finU (E := E) (n := n))) : Set (finU (E := E) (n := n)))
        (globLev S K' : Set (finU (E := E) (n := n))),
      ((Nat.card ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt γ)) ⊓
          (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU (E := E) (n := n))) : ℂ))⁻¹ *
        globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q)

end GlobalTheory.BCT
