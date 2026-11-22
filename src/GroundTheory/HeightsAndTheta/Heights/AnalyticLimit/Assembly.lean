module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.RegularizedMaxC2ExampleRealLine
public import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.ConvergenceRate
public import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Telescoping
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergyStep
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PPolyMaxLowerBound
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncPsh
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncTransfer
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBoundingKaehler
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TendstoLocallyUniformlyOnOfNhds
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassZero
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PKaehlerBound
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StatementsPullback
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.SystemIndependence
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListTailLog
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StBoundingKaehler
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TailDimZero
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UniformIntegrability
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PGlueRegularised
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPushDown

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open GroundTheory.Heights₂.Heights.LowerBoundFree

theorem BoundingKaehler.full : BoundingKaehler.Statement := BoundingKaehler.proof

theorem GreenMassZero.full : GreenMassZero.Statement := GreenMassZero.proof

theorem UniformIntegrability.of_greenMass (h₁ : GreenMassStep.Statement)
    (h₂ : GreenMassReplace.Statement) (h₃ : GreenMassError.Statement) :
    UniformIntegrability.Statement :=
  UniformIntegrability.proof GreenMassZero.full h₁ h₂ h₃

end GroundTheory.Heights₂.Heights.AnalyticLimit
