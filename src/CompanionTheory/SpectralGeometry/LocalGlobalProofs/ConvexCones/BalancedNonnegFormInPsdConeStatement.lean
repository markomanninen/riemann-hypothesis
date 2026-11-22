module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.BalancedNonnegFormInPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balanced_nonneg_form_in_psd_cone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (β : LinearMap.BilinForm ℤ X), β ∈ balForms bar X → (∀ y, 0 ≤ β y y) → toReal β ∈ psdCone (bar := bar) (X := X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.PsdConeMembership.toReal_mem_psdCone_of_nonneg | exact GlobalTheory.CompanionTheory.Ar.Fan.PsdConeMembership.toReal_mem_psdCone_of_nonneg | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.PsdConeMembership.toReal_mem_psdCone_of_nonneg <;> assumption)
