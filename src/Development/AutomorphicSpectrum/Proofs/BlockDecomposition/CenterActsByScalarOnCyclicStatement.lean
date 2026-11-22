module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterActsByScalarOnCyclic

@[expose] public section

open PositivityTheory.RgBcC.RealD (kF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_acts_by_scalar_on_cyclic : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F1 F2 : Fin n → Fin n → Module.End ℂ V), (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → ∀ (z : Module.End ℂ V), (∀ a b, z * F1 a b = F1 a b * z ∧ z * F2 a b = F2 a b * z) → ∀ (ev : V →ₗ[ℂ] ℂ) (c : ℂ), (∀ v, ev (z v) = c * ev v) → (∀ S : Submodule ℂ V, FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → (∀ w ∈ S, ev w = 0) → ∀ w ∈ S, w = 0) → ∀ x : V, z x = c • x := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.eq_smul_of_commute_of_ev | exact GlobalTheory.CompanionTheory.ModelS.eq_smul_of_commute_of_ev | (intros; apply GlobalTheory.CompanionTheory.ModelS.eq_smul_of_commute_of_ev <;> assumption)
