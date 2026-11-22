module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorAllOfTateDualityEulerChar
public import Formalism.AdmissibleDesigns.RestrictedSevenEightOfFull
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoAnnihilator_all_of_tateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.BKaAll D := by
  first | exact @GlobalTheory.BKaRows.bkaAll_of_hypotheses | exact GlobalTheory.BKaRows.bkaAll_of_hypotheses | (intros; apply GlobalTheory.BKaRows.bkaAll_of_hypotheses <;> assumption)
