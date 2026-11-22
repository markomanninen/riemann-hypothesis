module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularAtTranslate
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_at_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G) (t : T), toUnit (genPt R) ≫ σ = Γ.pt t → ∀ (f : T → FractionRing R) (g : Γ.G.left), Γ.RegularAt f (((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left g) → Γ.RegularAt (fun h => f (t * h)) g := by
  exact @QFGroup.regularAt_translate
