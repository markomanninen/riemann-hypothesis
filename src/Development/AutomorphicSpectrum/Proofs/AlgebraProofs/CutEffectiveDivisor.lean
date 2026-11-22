module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelIrreducibleBasicOpenConnected
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpVerticalPush
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpVerticalFibre
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpFibreDegree
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFiniteBirationalLength
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpDivisorPush
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AevalChartSubstMemOfMemBlowUpOf
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHorizontalComponentModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyDimensionInequality
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBundles
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlowUpFibreSemilocalStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectionFormulaDegreeStatement

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Num.CutClosed

open GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.AutoClose

theorem verticalPush : BlowUpVerticalPush.Statement.{0} :=
  BlowUpVerticalPush.proof (BlowUpVerticalFibre.proof BlowUpModel.full
    (BlowUpFibreDegree.proof NumbersDVR_HomLocRingLocal NumbersDVR_DivCycleHomLoc
      FiniteBirationalLength.full GlobalTheory.T.blow_up_fibre_semilocal) GlobalTheory.T.projection_formula_degree)

theorem main : CutByEffectiveDivisor.Statement.{0} :=
  CutByEffectiveDivisor.of_steps NumbersDVR_C3NoCommon
    (CommonFactorInduction.of_open ReesAlgebraDim.full BlowUpStrictTransform.proof
      NumbersDVR_C3BlowUpExcessDrop verticalPush (BlowUpDivisorPush.proof verticalPush)
      NumbersDVR_BlowUpHorizontalCorresp HorizontalComponentModel.proof)

end GlobalTheory.CompanionTheory.Ar.Num.CutClosed
