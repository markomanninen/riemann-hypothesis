module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasurableCuspWeightFamily
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_cusp_weight_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (X : Type) [MeasurableSpace X] (R : X → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ), (∀ x, (R x).form = form) → (∀ I, Measurable fun x => (R x).nz σ I) → (∀ x, BddAbove {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz σ I)}) → Measurable fun x => (R x).cuspW σ := by
  intro E _ _ _ g Λ _ _ Ψ _ X _ R σ form hform hnz _
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact measurable_of_empty _
  have : Module.Free ℤ Λ := (R x₀).free
  have : Module.Finite ℤ Λ := (R x₀).fin
  have : Countable (Submodule (𝓞 E) Λ) := by
    have : Countable Λ :=
      (Module.finBasis ℤ Λ).equivFun.toEquiv.injective.countable
    have : Countable (Submodule ℤ Λ) := by
      have hspan : Function.Surjective (fun s : Finset Λ => Submodule.span ℤ (s : Set Λ)) := by
        intro N
        obtain ⟨s, hs⟩ := (IsNoetherian.noetherian N : N.FG)
        exact ⟨s, hs⟩
      exact hspan.countable
    exact (Submodule.restrictScalars_injective ℤ (𝓞 E) Λ).countable
  let C : Submodule (𝓞 E) Λ → Prop := fun I =>
    I ≠ ⊥ ∧ GroundTheory.Heights₂.Heights.LowerBoundFree.IsSaturated I ∧
      GroundTheory.Heights₂.Heights.LowerBoundFree.IsIsoSub form I
  have hC (x : X) (I : Submodule (𝓞 E) Λ) : (R x).IsCusp I ↔ C I := by
    simp only [RiemLat.IsCusp, C, hform x]
  have hset (x : X) : {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz σ I)} =
      Set.range fun I : {I // C I} => -Real.log ((R x).nz σ I.1) := by
    ext y
    constructor
    · rintro ⟨I, hI, rfl⟩
      exact ⟨⟨I, (hC x I).1 hI⟩, rfl⟩
    · rintro ⟨I, rfl⟩
      exact ⟨I.1, (hC x I.1).2 I.2, rfl⟩
  have hsup : Measurable fun x => ⨆ I : {I // C I}, -Real.log ((R x).nz σ I.1) :=
    Measurable.iSup fun I => (Real.measurable_log.comp (hnz I.1)).neg
  have heq : (fun x => (R x).cuspW σ) =
      fun x => max 0 (⨆ I : {I // C I}, -Real.log ((R x).nz σ I.1)) := by
    funext x
    simp only [RiemLat.cuspW, hset x, iSup]
  rw [heq]
  exact measurable_const.max hsup
