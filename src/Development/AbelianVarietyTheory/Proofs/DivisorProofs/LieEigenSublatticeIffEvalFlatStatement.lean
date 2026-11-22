module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieEigenSublatticeIffEvalFlat
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAddValuationIntegerRingNormalizedIff

@[expose] public section

open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieEigenSublattice_iff_eval_flat : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a F → Function.Injective (evalVec (liftA hv a) N) → (∀ y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y) → (∀ x, x ∈ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F}) ↔ evalVec (liftA hv a) N x ∈ F) → (∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N, (∀ s, x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) → x ∈ F) → ∀ z : (Fin N → C) ⧸ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F τ, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) F) τ ↔ ∃ x : Fin N → RS (liftA hv a), proj (liftA hv a) ((Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.eigSub (liftA hv a) τ ((Fin N → RS (liftA hv a)) ⧸ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) ∧ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.quotMap (w := w) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F τ) (fun i => ((GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) N τ x i : Int0 v) : C)) = z := by
  first | exact @GlobalTheory.lie_eigenSub_iff_flat | exact GlobalTheory.lie_eigenSub_iff_flat | (intros; apply GlobalTheory.lie_eigenSub_iff_flat <;> assumption)
