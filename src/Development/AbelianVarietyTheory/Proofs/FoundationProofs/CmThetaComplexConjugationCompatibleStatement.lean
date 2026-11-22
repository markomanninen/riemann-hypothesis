module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatible
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmTheta_complexConjugation_compatible : ∀ D : D7, useBar D := by
  first | exact @GlobalTheory.ThetaConj.useBar_holds | exact GlobalTheory.ThetaConj.useBar_holds | (intros; apply GlobalTheory.ThetaConj.useBar_holds <;> assumption)
