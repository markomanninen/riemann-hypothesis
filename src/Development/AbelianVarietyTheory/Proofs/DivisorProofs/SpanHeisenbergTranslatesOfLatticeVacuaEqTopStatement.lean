module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanHeisenbergTranslatesOfLatticeVacuaEqTop
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumsCompEqIndex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalizedHeisenbergIntertwinerComp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntertwinerHeisenbergCocycleOfFixedVector
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilRepresentationHeisenberg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanHeisenbergTranslatesVacuumEqTop

@[expose] public section

open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_heisenberg_translates_of_lattice_vacua_eq_top : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ A : Submodule R X, SelfDual γ A → (∀ v : M, ∃ T : Submodule R X, idx A T ≠ 0 ∧ ∀ a ∈ A, (∀ t ∈ T, γ a t = 1) → W a v = v) → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ := by
  first | exact @GlobalTheory.FinWeil.span_translates_vacua | exact GlobalTheory.FinWeil.span_translates_vacua | (intros; apply GlobalTheory.FinWeil.span_translates_vacua <;> assumption)
