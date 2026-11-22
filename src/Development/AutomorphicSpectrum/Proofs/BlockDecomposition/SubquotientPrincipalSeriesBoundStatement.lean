module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientPrincipalSeriesBound
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
public import GroundTheory.AutomorphicForms.Satake

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subquotient_principal_series_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (α : Fin n → ℂˣ) (X V : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) X), IsSmooth ρ → ∀ (ι : ρ.IntertwiningMap (principalSeries k n (paramChar k α))), Function.Injective ι → ∀ (π : Representation ℂ (GL (Fin n) k) V), IsSubquotient π ρ → ∀ [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k)) [μ.IsHaarMeasure], IsSatakeParameter π μ α := by
  first | exact @GlobalTheory.CompanionTheory.HeckeSub.isSatakeParameter_subquotient | exact GlobalTheory.CompanionTheory.HeckeSub.isSatakeParameter_subquotient | (intros; apply GlobalTheory.CompanionTheory.HeckeSub.isSatakeParameter_subquotient <;> assumption)
