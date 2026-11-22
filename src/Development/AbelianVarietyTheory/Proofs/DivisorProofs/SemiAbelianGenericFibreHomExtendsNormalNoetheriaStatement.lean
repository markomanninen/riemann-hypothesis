module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGenericFibreHomExtendsNormalNoetheria
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_genericFibre_hom_extends_normal_noetherian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom φ → ∃ g : G ⟶ G, IsMonHom g ∧ (Over.pullback (jK R)).map g = φ := by
  first | exact @GlobalTheory.Mum.semiAbelian_end_generic_extends | exact GlobalTheory.Mum.semiAbelian_end_generic_extends | (intros; apply GlobalTheory.Mum.semiAbelian_end_generic_extends <;> assumption)
