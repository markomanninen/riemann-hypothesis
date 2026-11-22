module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceThetaLatticeHalvesSelfDualFrames
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_thetaLattice_halves_selfDual_frames : ∀ D : D7, SplitLattice D := by
  first | exact @GlobalTheory.SplitLatticeHalves.splitLattice | exact GlobalTheory.SplitLatticeHalves.splitLattice | (intros; apply GlobalTheory.SplitLatticeHalves.splitLattice <;> assumption)
