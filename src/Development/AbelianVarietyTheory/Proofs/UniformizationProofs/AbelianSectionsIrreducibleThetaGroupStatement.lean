module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSectionsIrreducibleThetaGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.abelian_sections_irreducible_theta_group : Laws → Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), (N : F) ≠ 0 → (∀ x : Over.mk p ⟶ P.A, x ^ N = 1 → ∃ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt = x) ∧ ∀ U : Submodule F (EA P p N), (∀ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt ^ N = 1 → ∀ v v' : EA P p N, IsActOf P.A P.L (N : ℤ) θ v.sec v'.sec → v ∈ U → v' ∈ U) → U = ⊥ ∨ U = ⊤ := by
  first | exact @GlobalTheory.ThetaIrred.main | exact GlobalTheory.ThetaIrred.main | (intros; apply GlobalTheory.ThetaIrred.main <;> assumption)
