module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryUnfoldingVolumeVectorStabilizer
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryUnfolding_volume_vectorStabilizer : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.QuotientMeasures → GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar → GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive → ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.Unfolding D := by
  first | exact @GlobalTheory.VolumeUnfolding.unfolding | exact GlobalTheory.VolumeUnfolding.unfolding | (intros; apply GlobalTheory.VolumeUnfolding.unfolding <;> assumption)
