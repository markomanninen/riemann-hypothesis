module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EtalePolynomialBaseChangeIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_polynomial_base_change_iff : ∀ (k A : Type) [CommRing k] [CommRing A] (N : ℕ), (Int.castRingHom (Localization.Away (N : k))).Etale → ∀ (φ : k →+* A), IsUnit (N : A) → ∀ (D : ℕ) (x : Fin D → A), (MvPolynomial.eval₂Hom φ x).Etale ↔ (MvPolynomial.eval₂Hom (Int.castRingHom A) x).Etale := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EtaleCoord.etale_eval₂Hom_iff_int | exact GlobalTheory.CompanionTheory.Ar.EtaleCoord.etale_eval₂Hom_iff_int | (intros; apply GlobalTheory.CompanionTheory.Ar.EtaleCoord.etale_eval₂Hom_iff_int <;> assumption)
