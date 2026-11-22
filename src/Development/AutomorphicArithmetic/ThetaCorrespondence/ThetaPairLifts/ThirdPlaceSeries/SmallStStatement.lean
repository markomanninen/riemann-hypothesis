module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStAltAlt

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_estimate : _root_.GlobalTheory.ExpTie.SmallnessCondition := by
  first | exact @_root_.GlobalTheory.ExpTie.smallSt_alt | exact _root_.GlobalTheory.ExpTie.smallSt_alt | (intros; apply _root_.GlobalTheory.ExpTie.smallSt_alt <;> assumption)
end
