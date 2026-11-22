module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsDenOfOpen

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem btOrder_eq_of_open_cover : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of A)), Γ.IsEmb A j → IsOpenImmersion j → Γ.TranslatesCover A j ⊤ → Γ.btOrder ⊤ = A :=
  @PositivityTheory.HtPt.Mh.char

end GlobalTheory.CompanionTheory.Ar.BT
