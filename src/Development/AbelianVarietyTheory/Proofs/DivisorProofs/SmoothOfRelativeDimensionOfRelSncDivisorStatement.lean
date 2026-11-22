module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfRelSncDivisor
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_relSncDivisor : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), RelSnc f d L σ → SmoothOfRelativeDimension d f := by
  first | exact @GlobalTheory.LogPair.smooth_of_relSnc | exact GlobalTheory.LogPair.smooth_of_relSnc | (intros; apply GlobalTheory.LogPair.smooth_of_relSnc <;> assumption)
