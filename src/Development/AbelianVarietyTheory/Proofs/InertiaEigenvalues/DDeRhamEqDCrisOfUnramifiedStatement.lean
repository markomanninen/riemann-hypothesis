module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DDeRhamEqDCrisOfUnramified
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dDeRham_eq_dCris_of_unramified : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D := by
  first | exact @GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange | exact GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange | (intros; apply GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange <;> assumption)
