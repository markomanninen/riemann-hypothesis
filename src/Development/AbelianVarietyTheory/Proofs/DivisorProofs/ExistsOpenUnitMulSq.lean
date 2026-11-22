module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallHeightOneExistsDvdMul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGermPrimeIdealMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGermInjectiveClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionSquareUnitsLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSquareFactorizationSections

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SquareNear

theorem stalk_props : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ x : G₁.left, IsDomain (G₁.left.presheaf.stalk x) ∧ IsNoetherianRing (G₁.left.presheaf.stalk x) ∧ IsIntegrallyClosed (G₁.left.presheaf.stalk x) := by
  intro R' _ _ _ hA G₁ _ _ hG x
  obtain ⟨_, -, _, -⟩ := hA
  haveI := hG.smooth
  have hS : GlobalTheory.IsNormalScheme (Sp R') := inferInstance
  have h := GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth G₁.hom
    ((GlobalTheory.isNormalScheme_iff _).mp hS) x
  haveI : IsLocallyNoetherian G₁.left := LocallyOfFiniteType.isLocallyNoetherian G₁.hom
  exact ⟨h.1, inferInstance, h.2⟩

end GlobalTheory.SquareNear
