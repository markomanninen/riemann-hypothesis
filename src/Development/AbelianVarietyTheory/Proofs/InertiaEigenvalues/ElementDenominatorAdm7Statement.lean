module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ElementDenominatorAdm7
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adm7_elementDenominator : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm7 D := by
  first | exact @GlobalTheory.elementDenominator_adm7 | exact GlobalTheory.elementDenominator_adm7 | (intros; apply GlobalTheory.elementDenominator_adm7 <;> assumption)
