module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialWedgeDecompositionDiscreteSeriesLargeGaps
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.PieriTensorDecompositionStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorDecompositionParametersStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesParameterUniqueStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorDecompositionInjectiveParameters

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivialWedgeDecomposition_discreteSeries_largeGaps : BranchingSupport.HypsG → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (F F' : (Fin (2 * r + k + 1) → ℤ) → BranchingSupport.Rep k r) (ν : Fin (2 * r + k + 1) → ℤ), BranchingSupport.Num k r lam u b bv ga h q0 → BranchingSupport.IsFamG lam q0 F → BranchingSupport.IsFamG lam q0 F' → BranchingSupport.n1 ν + 2 ≤ q0 → ∃ io pr ep, BranchingSupport.TensH (BranchingSupport.cmp 0) (BranchingSupport.cmp 0 (Formalism.QuantumDeterminants.Hpk k r)) (F ν) (fun I : BranchingSupport.Sub (2 * r + k + 1) 0 => F' (ν + BranchingSupport.eZ I.1)) io pr ep := by
  first | exact @GlobalTheory.TrivWedge.tensH_trivial | exact GlobalTheory.TrivWedge.tensH_trivial | (intros; apply GlobalTheory.TrivWedge.tensH_trivial <;> assumption)
