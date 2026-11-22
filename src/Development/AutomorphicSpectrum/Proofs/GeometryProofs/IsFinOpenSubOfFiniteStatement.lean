module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubOfFinite
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinOpenSub_of_finite : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → (∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U) → Γ.IsFinOpenSub U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isFinOpenSub_of_closedFibre | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isFinOpenSub_of_closedFibre | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isFinOpenSub_of_closedFibre <;> assumption)
