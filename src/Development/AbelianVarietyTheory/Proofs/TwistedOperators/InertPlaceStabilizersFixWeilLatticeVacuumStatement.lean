module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceStabilizersFixWeilLatticeVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_stabilizers_fix_weil_lattice_vacuum : ∀ D : D7, InertVacuumFixed D := by
  first | exact @GlobalTheory.PlaceTensor.inertVacuumFixed | exact GlobalTheory.PlaceTensor.inertVacuumFixed | (intros; apply GlobalTheory.PlaceTensor.inertVacuumFixed <;> assumption)
