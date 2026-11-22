module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoFiniteTrivialRepUnramifiedColumnPlacesA
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedTrivialH1f_of_decl : ∀ (D : D7) (i : D.nd.Loc) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i), Formalism.MainNotions.EmbeddingTypes.UnramifiedTrivialH1f (D := D) i dc := by
  first | exact @GlobalTheory.ColumnUnramified.blochKatoFinite_trivialRep_unramified_columnPlaces | exact GlobalTheory.ColumnUnramified.blochKatoFinite_trivialRep_unramified_columnPlaces | (intros; apply GlobalTheory.ColumnUnramified.blochKatoFinite_trivialRep_unramified_columnPlaces <;> assumption)
