module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundlePullbackFieldExtensionIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBigLineBundle_pullback_fieldExtension_iff : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q → topologicalKrullDim X = topologicalKrullDim Y → ∀ L : LB Y, L.IsLB → ((letI := algebraΓOfHom q; IsBig E (L.pull π)) ↔ (letI := algebraΓOfHom p; IsBig k L)) := by
  first | exact @GlobalTheory.BigFieldChange.isBig_pull_iff | exact GlobalTheory.BigFieldChange.isBig_pull_iff | (intros; apply GlobalTheory.BigFieldChange.isBig_pull_iff <;> assumption)
