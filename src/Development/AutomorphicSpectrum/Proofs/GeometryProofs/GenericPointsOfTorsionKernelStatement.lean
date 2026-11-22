module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsOfTorsionKernel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_of_torsion_kernel : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsSemiAbelian B → ∀ (N : ℕ), 1 ≤ N → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] [IsCommMonObj A] (j : A ⟶ B) [IsMonHom j], IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B] → (∀ g : A.left, (A.hom g).asIdeal = ⊥ → ∃ (κ : genPt R ⟶ A) (x : Spec (CommRingCat.of (FractionRing R))), κ.left x = g) → ∃ (C : Type) (_ : CommGroup C) (Γ : QFGroup R C) (φ : Γ.G ≅ A), IsMonHom φ.hom ∧ Γ.IsTorsionAlong B (𝟙 _) N (φ.hom.left ≫ j.left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_kernel | exact GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_kernel | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_kernel <;> assumption)
