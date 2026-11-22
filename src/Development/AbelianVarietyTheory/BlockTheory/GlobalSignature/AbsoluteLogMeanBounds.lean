module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AbsoluteLogMeanBounds

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients Classical

def kronBound (D : D7) : ℝ :=
  (1 / 2) * (Real.log (Real.sqrt (D.host.d : ℝ)) - Real.eulerMascheroniConstant + logDerivativeAtOne D)

end GlobalTheory.IndefiniteRowSideFullHecke.AbsoluteLogMeanBounds
