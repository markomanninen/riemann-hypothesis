module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEigenfunctionBound
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst

@[expose] public section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_eigenfunction_bound : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ →
  IsFundamentalDomain (latticeGL E N) F μ → ∃ C₀ : ℝ, ∀ ψ : GA E N → ℂ, Continuous ψ → (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) →
  (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) → (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 →
  ∀ (x : GA E N) (k : ℕ), {γ : GA E N | γ ∈ latticeGL E N ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k →
    ‖ψ x‖ ^ 2 ≤ C₀ * k := by
  intro E _ _ _ N _ _ μ _ α δ F hα hc hδ hF
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  exact GlobalTheory.CompanionTheory.Conc.BesselPt.pointwise μ (latticeGL E N) hα hc hδ hF
