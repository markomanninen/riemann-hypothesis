module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtAlgebraMapSgnAdSubOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realLift_parity : GlobalTheory.RealLift.Parity := by
  first | exact @GlobalTheory.RealLift.even_im_hermitian_sub | exact GlobalTheory.RealLift.even_im_hermitian_sub | (intros; apply GlobalTheory.RealLift.even_im_hermitian_sub <;> assumption)
