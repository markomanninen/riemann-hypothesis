module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousCuspNormFamily
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_cusp_norm_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), (∀ v, Continuous fun x => (R x).P v) → (Continuous fun x => (R x).Hm) → Continuous fun x => (R x).nz σ I := by
  intro E _ _ _ g Λ _ _ Ψ _ X _ R σ I hP hH
  by_cases h : ∃ r v, GroundTheory.Heights₂.Heights.LowerBoundFree.IsNzFamily I r v
  · have hcont : Continuous fun x => (R x).nzOf σ I h.choose_spec.choose :=
      GlobalTheory.CompanionTheory.Ar.Cusp.NzCont.continuous_nzOf R hP hH σ I _
    simpa only [RiemLat.nz, dite_eq_left h] using hcont
  · simpa only [RiemLat.nz, dite_eq_right h] using
      (continuous_const : Continuous fun _ : X => (1 : ℝ))
