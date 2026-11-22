module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af

namespace UpperTheory.V.Published

section Sys

variable {F : Type} [Field F] [NumberField F]

def SelfTw (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (η : HChar F) : Prop :=
  ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, η.UnrAt v ∧ ∃ B, sat v B ∧ B.map (· * η.val v) = B

variable (E : Type) [Field E] [NumberField E] [Algebra F E]

def IsNormChar (η : HChar F) : Prop :=
  η ≠ 1 ∧ η ^ Module.finrank F E = 1 ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ f : ℕ,
    normV w = normV (w.under (𝓞 F)) ^ f → η.val (w.under (𝓞 F)) ^ f = 1


variable {E} in
def WeakBC (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (satE : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ → Prop) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f →
    ∃ B, sat (w.under (𝓞 F)) B ∧ satE w (B.map (· ^ f))

end Sys

end UpperTheory.V.Published
