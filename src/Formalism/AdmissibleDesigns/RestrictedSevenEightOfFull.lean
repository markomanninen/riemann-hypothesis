module

public import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.WildPro
public import Formalism.SharpRestriction.LevelLetterCocycles.QpowOfTw
public import Formalism.LocalRingCardinality.SpanPowerMembership.Places

@[expose] public section

noncomputable section

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.Rows

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N

variable (D : D7)

def AllDesignConditions : Prop :=
  ∀ i : D.nd.Loc, D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 →
    ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
      (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
      GoodR D.nd i r → TruncatedSeriesCountingIdentities.admitted i r ρ π dc lenRow e' cB → LargeLevelLemmas.adm51 i r ρ π

def BKaAll : Prop := ∀ i : D.nd.Loc, LargeLevelLemmas.BlochKatoAnnihilators i

def FinAll : Prop := ∀ i : D.nd.Loc, LargeLevelLemmas.tateH1FinitenessAtPlacesOver i

end Formalism.MainNotions.N.K.Rows

end
