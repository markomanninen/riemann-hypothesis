module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatTensorIndicatorCharacterFacts
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

@[expose] public section

open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_tensor_indicator_character_facts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'], (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), Ψ ∈ SB (Matrix n n' k) → a ∈ SB (n → k) → GlobalTheory.FinPl.tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) ∧ (∀ (Λ : Submodule 𝒪[k] (n → k)), Λ.IsFullLattice k → GlobalTheory.FinPl.vecInd Λ ∈ SB (n → k)) ∧ ∀ (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n), GlobalTheory.FinPl.charInd χ Q ∈ SB (n → k) := by
  intro k _ _ _ _ n n' _ _ _ _
  refine ⟨fun Ψ a hΨ ha => GlobalTheory.FinPl.Comm.tensCol_mem hΨ ha, ?_,
    fun χ Q => GlobalTheory.FinPl.SBFacts.charInd_mem χ Q⟩
  intro Λ hΛ
  have := hΛ
  exact GlobalTheory.FinPl.Comm.vecInd_mem Λ
