module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOrderEmbedding
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClOfSelf

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_order_embedding : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n p N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (zz : Fin n → IrrGL (k := k)) (σ : Fin p ↪o Fin n) (c : Fin n → ℕ), (∀ a, c (σ a) = (zz (σ a)).1) → (∀ j, j ∉ Set.range σ → c j = 0) → ∀ (hz : ∑ a, (zz (σ a)).1 = N) (f : (Σ j, Fin (c j)) ≃ Fin N), jm (fun a => zz (σ a)) hz π ≠ 0 → jhMult (piTensor fun j => (clOf (zz j) (c j)).rep.ρ) (jac f π) ≠ 0 := by
  exact @GlobalTheory.CompanionTheory.WordProd.RowCell.jhMult_row
