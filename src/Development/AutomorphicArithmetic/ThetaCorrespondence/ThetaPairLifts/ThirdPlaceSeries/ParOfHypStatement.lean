module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParOfHyp

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parOf_hyp_at_pts : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).Hyp := by
  first | exact @_root_.GlobalTheory.ExpTie.parOf_hyp_alt | exact _root_.GlobalTheory.ExpTie.parOf_hyp_alt | (intros; apply _root_.GlobalTheory.ExpTie.parOf_hyp_alt <;> assumption)
end
