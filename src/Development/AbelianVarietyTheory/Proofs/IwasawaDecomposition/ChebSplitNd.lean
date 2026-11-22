module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.ChebSplitDense

theorem chebSplit (hC : GlobalTheory.Published.ChebotarevDegreeOne) {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    (N : NData R H what₂) : GlobalTheory.RowTie.ChebSplit N := by
  intro S
  obtain ⟨A, hA, hsp⟩ := GlobalTheory.FrobDense.exists_finite_split H
  refine (hC.dense (F := H.E) (Ω := N.Om) (hA.union S.finite_toSet)).mono ?_
  rintro σ ⟨v, hv, hd, B, hB, hσ⟩
  simp only [Set.mem_union, Finset.mem_coe, not_or] at hv
  exact ⟨v, hv.2, hsp v hv.1 hd, B, hB, hσ⟩

theorem chebSplit_nd : GlobalTheory.Published.ChebotarevDegreeOne → ∀ D : D7, GlobalTheory.RowTie.ChebSplit D.nd :=
  fun hC D => chebSplit hC D.nd

end GlobalTheory.ChebSplitDense
