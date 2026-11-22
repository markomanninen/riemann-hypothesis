module

public import Mathlib
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt Filter Topology

def cxSimple {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (w : ((k : K) → ι k) → ℂ) : Prop :=
  ∃ (y : Fin e → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ), IsSetSheet S Ψ y w γ ∧
    ∀ᶠ q in 𝓝 (y, w), q.2 ∈ setFibre S Ψ q.1 → q.2 = segre (γ q.1)

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
