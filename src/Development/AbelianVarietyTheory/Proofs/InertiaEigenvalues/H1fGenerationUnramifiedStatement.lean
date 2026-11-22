module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGenerationUnramified
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h1fGeneratorBoundAll_loc : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBoundAll D.loc := by
  first | exact @GlobalTheory.GenCountUnram.admGenL_all | exact GlobalTheory.GenCountUnram.admGenL_all | (intros; apply GlobalTheory.GenCountUnram.admGenL_all <;> assumption)
