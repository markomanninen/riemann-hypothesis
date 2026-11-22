module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuumIsometryOfSkeletonDatum
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VacuumFockVectors

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D := by
  first | exact @GlobalTheory.vacuumFock_all_records | exact GlobalTheory.vacuumFock_all_records | (intros; apply GlobalTheory.vacuumFock_all_records <;> assumption)
