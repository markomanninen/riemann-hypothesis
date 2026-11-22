module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationOfData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpOmjExtIff

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

def CovBy {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (Φ : C → Prop) (S : C) : Prop :=
  ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧
    ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → Φ S'

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
