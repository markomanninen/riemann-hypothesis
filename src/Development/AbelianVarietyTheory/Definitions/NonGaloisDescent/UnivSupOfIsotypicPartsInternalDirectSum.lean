module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.SupLaw.Model

open GlobalTheory.TwAll

variable (D : D7)

abbrev Pt (j : ℕ) : Type := {_g : G0g D.nd // j ∈ Finset.Icc 1 D.R.m}

abbrev KK (i : D.ntw.Tw) : Type := FractionRing (D.ntw.O i)

variable (A : ∀ (i : D.ntw.Tw) (j : ℕ), ℕ → PlE D.host → Module.End (KK D i) (Pt D j → KK D i))
  (s : ∀ i : D.ntw.Tw, ℕ → KK D i)



end GlobalTheory.SupLaw.Model

end
