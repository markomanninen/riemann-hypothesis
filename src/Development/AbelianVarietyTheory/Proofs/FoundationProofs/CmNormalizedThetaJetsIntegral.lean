module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LevelRestrictionOfGroupLawHolds
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaCubeRelationIntegralFormalGroupBiadditiveStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaPointsIntegralNormConjugateLawsStatement

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaJets

theorem jetsPh_all : ∀ D : D7, GL3Theta.jetsPh D := fun D =>
  Formalism.MainNotions.Ext.CutA.jetsPh_of' Formalism.MainNotions.Ext.CutA.jetsHigh_holds Formalism.MainNotions.Ext.CutA.jetsOne_holds
    Formalism.MainNotions.Ext.CutA.jetsTwo_holds D (GlobalTheory.T.theta_cube_relation_integral_formalGroup_biadditive D).1 (GlobalTheory.T.cmThetaPoints_integral_norm_conjugate_laws D).2.1 (GlobalTheory.T.cmThetaPoints_integral_norm_conjugate_laws D).2.2

end GlobalTheory.ThetaJets
