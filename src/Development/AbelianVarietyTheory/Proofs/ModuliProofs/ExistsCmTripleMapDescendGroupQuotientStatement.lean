module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCmTripleMapDescendGroupQuotient
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmTripleMap_descend_groupQuotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (U U' X' : Scheme.{0}) (ρ : Γ →* Aut U) (r : U ⟶ U') (t : SAB H U) (t' : SAB H U') (t₁ : SAB H X') (τ : Γ →* Aut t.G.left) (ν : SABMap t t' r) (j : U' ⟶ X') (n : SABMap t t₁ (r ≫ j)), (IsAffineHom r ∧ (∀ g, (ρ g).asIso.hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsReduced U → IsProper t.G.hom → (∀ g, (τ g).asIso.hom ≫ t.G.hom = t.G.hom ≫ (ρ g).asIso.hom ∧ (τ g).asIso.hom ≫ ν.φ = ν.φ ∧ (τ g).asIso.hom ≫ n.φ = n.φ) → ∃ n' : SABMap t' t₁ j, ν.φ ≫ n'.φ = n.φ := by
  first | exact @GlobalTheory.exists_sabMap_of_quotient | exact GlobalTheory.exists_sabMap_of_quotient | (intros; apply GlobalTheory.exists_sabMap_of_quotient <;> assumption)
