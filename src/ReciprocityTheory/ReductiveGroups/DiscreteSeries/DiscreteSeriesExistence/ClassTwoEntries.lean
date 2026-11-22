module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.RightDerivativeZeroOutsideSupport
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IntegrableComplexContinuousBoundedSupport

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem r0bG : Formalism.REAL.SmoothVectorGrowthBound :=
  Formalism.REAL.square_integrable_of_lipschitz Formalism.REAL.log_frobenius_lipschitz_holds Formalism.REAL.integral_right_derivative_zero

end ReciprocityTheory.ChartRestriction.DS
