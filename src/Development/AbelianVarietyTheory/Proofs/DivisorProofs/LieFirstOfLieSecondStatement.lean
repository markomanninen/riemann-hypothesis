module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieFirst_of_lieSecond' : GlobalTheory.RealLift.LieSecond → GlobalTheory.RealLift.LieFirst := by
  first | exact @GlobalTheory.RealLift.LieFirstPf.lieFirst_of_lieSecond | exact GlobalTheory.RealLift.LieFirstPf.lieFirst_of_lieSecond | (intros; apply GlobalTheory.RealLift.LieFirstPf.lieFirst_of_lieSecond <;> assumption)
