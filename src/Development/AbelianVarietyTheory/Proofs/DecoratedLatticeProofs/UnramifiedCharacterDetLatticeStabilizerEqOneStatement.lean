module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharacterDetLatticeStabilizerEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

@[expose] public section

open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule 𝒪[k] (n → k)), L.IsFullLattice k → ∀ g ∈ latStab L, ∀ μ : kˣ →* ℂˣ, IsUnram μ → μ (Matrix.GeneralLinearGroup.det g) = 1 := by
  intro k _ _ _ _ n _ _ L hL g hg μ hμ
  letI := hL
  exact GlobalTheory.LatPair.Det.isUnram_det_latStab k n L inferInstance g hg μ hμ
