module

public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameFixedLift

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.AdmissibleDictionary

theorem main : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i := by
  intro D i
  exact GlobalTheory.TameFixedLift.main D.nd i

end GlobalTheory.AdmissibleDictionary
