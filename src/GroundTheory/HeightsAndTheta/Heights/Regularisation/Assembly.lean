module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PMaxOscillation
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PMollifierLowerBound
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartComparison
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PCutoffs
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PGlueRegularised
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.ChartFun
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsCompactImageClosureMid
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PExpExtension
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PosSemidefOfIntQuadNonneg
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PKernelPositive
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PImTauBounds
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PHodgeDerivative
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PAnalyticDerivBound
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PInvEntryBound
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PInvEntryDeriv
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PMatrixDetDeriv
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PGramEntryDeriv
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLogDetGramDeriv

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

theorem GlueRegularised.full : GlueRegularised.Statement :=
  GlueRegularised.proof

theorem KernelPositive.full : KernelPositive.Statement :=
  kernelPositive_statement

theorem Tau0Holomorphic.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    Tau0Holomorphic.Statement :=
  Tau0Holomorphic.proof (ExpQuadMonomial.proof hE hO hD)

theorem ImTauBounds.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    ImTauBounds.Statement :=
  ImTauBounds.proof (Tau0Holomorphic.cond hE hO hD) KernelPositive.full

theorem HodgeDerivative.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    HodgeDerivative.Statement :=
  have hInv : InvEntryDeriv.Statement := InvEntryDeriv.proof InvEntryBound.proof
  HodgeDerivative.proof (ImTauBounds.cond hE hO hD) (Tau0Holomorphic.cond hE hO hD)
    AnalyticDerivBound.proof hInv
    (LogDetGramDeriv.proof InvEntryBound.proof hInv MatrixDetDeriv.proof GramEntryDeriv.proof)

end GroundTheory.Heights₂.Heights.Regular
