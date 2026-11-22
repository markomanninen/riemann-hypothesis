module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderFlatBaseChange
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_flat_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → Γ'.btOrder ⊤ = extOrder (algebraMap R R') (Γ.btOrder ⊤) := by
  exact @GlobalTheory.CompanionTheory.Ar.BT.FlatBC.btOrder_flat_baseChange
