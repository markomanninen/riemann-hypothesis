module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.SmoothDesignExistence.ContinuousHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAtAll

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAdm

theorem fontaineProperties_all_places : ∀ (D : D7) (i : D.nd.Loc), Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i :=
  fun D i => Formalism.MainNotions.Pk.font_of_all_places (fun l _ K LL => GlobalTheory.FontaineAll.fontaineAt_all D l K LL) i

end GlobalTheory.FontaineAdm
