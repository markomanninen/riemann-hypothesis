module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleCentralizerPointsOfCommutantAdj
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_centralizer_points_of_commutant_adjoint : GlobalTheory.RegSS.PointsCommutant → GlobalTheory.RegSS.PointsAdjoint → GlobalTheory.RegSS.PointsCentraliser := by
  first | exact @GlobalTheory.RegSS.pointsCentraliser_of_commutant_of_adjoint | exact GlobalTheory.RegSS.pointsCentraliser_of_commutant_of_adjoint | (intros; apply GlobalTheory.RegSS.pointsCentraliser_of_commutant_of_adjoint <;> assumption)
