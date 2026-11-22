module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorBtOrder
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominator_btOrder :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T]
      (Γ : GlobalTheory.CompanionTheory.Ar.BT.QFGroup R T),
      ∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤ :=
  @GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank
