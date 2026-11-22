module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicRealisationHolomorphicMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPartMul

@[expose] public section

open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_separable_commutative : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (γ g h : GL ι K),
  (γ : Matrix ι ι K).charpoly.Separable → g * γ = γ * g → h * γ = γ * h → g * h = h * g := by
  first | (exact @GlobalTheory.CentSep.centraliser_comm_of_separable) | (exact GlobalTheory.CentSep.centraliser_comm_of_separable) | (intros; apply GlobalTheory.CentSep.centraliser_comm_of_separable  <;> assumption)
