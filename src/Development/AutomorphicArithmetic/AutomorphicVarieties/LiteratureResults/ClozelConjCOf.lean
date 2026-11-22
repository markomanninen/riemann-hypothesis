module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af

namespace UpperTheory.V.Lit

def FinExC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∃ τ, IsFinComp π τ

end UpperTheory.V.Lit
