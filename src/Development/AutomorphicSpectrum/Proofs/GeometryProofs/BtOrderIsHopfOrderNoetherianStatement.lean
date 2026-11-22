module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrderNoetherian
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_isHopfOrder_noetherian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), IsHopfOrder (Γ.btOrder ⊤) := by
  exact @GlobalTheory.CompanionTheory.Relay.btOrder_isHopfOrder_noetherian
