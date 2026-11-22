module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceSt

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupLe_traceSt : _root_.GlobalTheory.BigOn.Exp.TupLe.TraceCondition := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TupLe.traceSt_alt | exact _root_.GlobalTheory.BigOn.Exp.TupLe.traceSt_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.TupLe.traceSt_alt <;> assumption)
end
