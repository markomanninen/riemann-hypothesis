module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosed
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_principal_ideal_saturated_closed : ∀ (l : ℕ) [Fact l.Prime] (ι : Ainf l), IsUnit (inclW l ι) → ∀ (r : ℕ) (x : WCb l), (∀ n : ℕ, ∃ a : Ainf l, (l : WCb l) ^ n ∣ (l : WCb l) ^ r * x - inclW l (ι * a)) → ∃ a : Ainf l, x = inclW l (ι * a) := by
  first | exact @GlobalTheory.AinfSat.mem_ideal_of_saturated | exact GlobalTheory.AinfSat.mem_ideal_of_saturated | (intros; apply GlobalTheory.AinfSat.mem_ideal_of_saturated <;> assumption)
