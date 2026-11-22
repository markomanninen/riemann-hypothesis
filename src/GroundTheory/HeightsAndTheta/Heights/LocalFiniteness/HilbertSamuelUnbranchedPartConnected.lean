module

public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelGrowthOffHypersurfacePolynomial
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.NumbersDVRC3ResidualContractionComponent
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersLocalIntegralClosureFinite
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegreeRatio
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitFiniteSum
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeEuclMass
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeLocalFlat
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PManifoldZerosComplementConnected
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsFurther
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsRest
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleHomLoc
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionForms
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Assembly
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParAlgIndep
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBGeneric
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBLinInj

@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalFinite.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFinite.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalFinite.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalIntegral GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_LocalIntegralClosureFinite GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DegZeroLocNoetherian

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalFlat.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalFlat.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.ConeLocalFlat.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConePolyLocalization

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_DivCycleHomLoc.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_HomLocRingLocal

theorem GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualCompare.{u} : GroundTheory.Heights₂.Heights.NumbersDVR.ResidualComparison.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.NumbersDVR.ResidualComparison.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3BlowUpPieces GroundTheory.Heights₂.Heights.NumbersDVR.ResidualDisjoint.proof GroundTheory.Heights₂.Heights.AutoClose.NumbersDVR_C3ResidualContraction

theorem GroundTheory.Heights₂.Heights.AutoClose.TubeEuclMass : GroundTheory.Heights₂.Heights.TubeEuclMass.Statement :=
  @GroundTheory.Heights₂.Heights.TubeEuclMass.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.TubeCollarMass GroundTheory.Heights₂.Heights.AutoClose.TubeDeepMass
