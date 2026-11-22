module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationPullbackInjectiveLocStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHomStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisClosureLocalDomainExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisActionOnUniformisedGroupPulledDataStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianGaloisDescentStatement

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem has_of_hasFin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)), HasFin D → Has D := by
  intro R _ _ _ hR D ⟨R', _, _, _, ρ, D', hρ, ⟨p⟩, hH⟩
  obtain ⟨R'', _, _, _, σ, hσ, hσl, hc, hg⟩ := GlobalTheory.T.exists_galois_closure_local_domain_extension R R' ρ hR hρ
  obtain ⟨D'', ⟨q⟩⟩ := GlobalTheory.T.exists_degenerationData_pullback_injective_localHom R' R'' σ hσ.2.1 hσl D'
  obtain ⟨G'', _, _, A'', hG, ⟨U⟩⟩ := GlobalTheory.T.hasSemiAbelianUniformisation_pullback_injective_local R' R'' σ hρ.1 hσ.1 hσ.2.1 hσl D' D'' ⟨q⟩ hH
  obtain ⟨r⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hρ.2.1 hσ.2.1 p q
  obtain ⟨act⟩ := GlobalTheory.T.exists_galoisAction_on_uniformisedGroup_pulledData R R'' (σ.comp ρ) hR hc hg D D'' r A'' G'' hG U
  exact GlobalTheory.T.uniformised_semiAbelian_galois_descent R R'' (σ.comp ρ) hR hc hg D D'' r A'' G'' hG U act

end GlobalTheory.Mum
