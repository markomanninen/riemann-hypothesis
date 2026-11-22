module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBaseChangeSections

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.flat_base_change_sections : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) [QuasiCompact f] [IsSeparated f] (L : LB X), φ.Flat → IsPullback π f' f (spMap φ) → L.IsLB → ∀ σ : (L.pull π).Sec, ∃ (n : ℕ) (c : Fin n → R') (τ : Fin n → L.Sec), ∀ i, σ.f i = ∑ a, cstOn f' _ (c a) * (Cartier.secPull (τ a) π).f i := by
  first | exact @_root_.GlobalTheory.SecFlatBC.exists_sum_secPull | exact _root_.GlobalTheory.SecFlatBC.exists_sum_secPull | (intros; apply _root_.GlobalTheory.SecFlatBC.exists_sum_secPull <;> assumption)
