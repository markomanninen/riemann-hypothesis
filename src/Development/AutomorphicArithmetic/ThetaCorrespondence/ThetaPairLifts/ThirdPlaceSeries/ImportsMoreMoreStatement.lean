module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalOfArtinReciprocity
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsNoCut
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreMore

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalPass_of_globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.Pass.GlobalStatement := by
  first | exact @_root_.GlobalTheory.StepGlobalPf.main_alt_alt | exact _root_.GlobalTheory.StepGlobalPf.main_alt_alt | (intros; apply _root_.GlobalTheory.StepGlobalPf.main_alt_alt <;> assumption)
end
