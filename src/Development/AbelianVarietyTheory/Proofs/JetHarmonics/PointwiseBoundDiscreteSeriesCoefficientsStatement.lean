module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundDiscreteSeriesCoefficients
public import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Formalism.HermitianCurvature.HerGenC

@[expose] public section

open BpJoin Formalism.FourierDecayAlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointwiseBound_discreteSeries_coefficients : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ThmBpDS := by
  first | exact @GlobalTheory.BpDiscreteSeriesTwoInputs.pointwise_bound_discreteSeries | exact GlobalTheory.BpDiscreteSeriesTwoInputs.pointwise_bound_discreteSeries | (intros; apply GlobalTheory.BpDiscreteSeriesTwoInputs.pointwise_bound_discreteSeries <;> assumption)
