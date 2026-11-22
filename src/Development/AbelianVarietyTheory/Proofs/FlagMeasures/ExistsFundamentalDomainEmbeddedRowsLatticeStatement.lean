module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalDomainEmbeddedRowsLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamentalDomain_embeddedRowsLattice : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (k : ℕ) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), Submodule.IsFullLattice E Λ₀ → Submodule.IsFullLattice E Λ' → ∃ P : Set (VecInf E k), MeasurableSet P ∧ volume P = ENNReal.ofReal (covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) ^ k * (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * k) / covAt E k (latAt E k Λ' (oneInf E k)))) ∧ (∀ T : VecInf E k, ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ (fun w b => T w b + w.embedding (τ b)) ∈ P) ∧ ∀ (T : VecInf E k) (τ : Fin k → E), (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) → T ∈ P → (fun w b => T w b + w.embedding (τ b)) ∈ P → τ = 0 := by
  intro E _ _ hE k Λ₀ Λ' h₀ h'
  first
  | exact GlobalTheory.RowDomain.rowDomain E hE k Λ₀ Λ' h₀ h'
  | exact GlobalTheory.RowDomain.rowDomain E hE k Λ₀ Λ' h₀.toIsLattice h'.toIsLattice
