module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaCubeRelationIntegralFormalGroupBiadditive
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_cube_relation_integral_formalGroup_biadditive : ∀ D : D7, GL3Theta.cube D ∧ GL3Theta.addInt D ∧ GL3Theta.beBiadd D := by
  first | exact @GlobalTheory.ThetaCube.cube_addInt_beBiadd | exact GlobalTheory.ThetaCube.cube_addInt_beBiadd | (intros; apply GlobalTheory.ThetaCube.cube_addInt_beBiadd <;> assumption)
