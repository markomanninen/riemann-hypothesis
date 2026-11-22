module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteAdeleExtendedCharacterOfCurve
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdeleExtendedCharacter_of_curve : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ ψ : AE D → ℂ, IsPsi D cc δ ψ := by
  first | exact @GlobalTheory.FinWeil.AdelicChar.exists_psi | exact GlobalTheory.FinWeil.AdelicChar.exists_psi | (intros; apply GlobalTheory.FinWeil.AdelicChar.exists_psi <;> assumption)
