module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivati
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine := by
  first | exact @GlobalTheory.VacLn.vacLine_of_derEx | exact GlobalTheory.VacLn.vacLine_of_derEx | (intros; apply GlobalTheory.VacLn.vacLine_of_derEx <;> assumption)
