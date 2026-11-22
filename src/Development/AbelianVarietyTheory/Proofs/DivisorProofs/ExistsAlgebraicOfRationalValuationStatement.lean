module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicOfRationalValuation
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraic_of_rational_valuation : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ q : ℚ, ∃ c : ℂ, c ≠ 0 ∧ Sz l lam (-(q : ℝ)) c ∧ Sz l lam q c⁻¹ := by
  first | exact @GlobalTheory.QFam.exists_sz_scale | exact GlobalTheory.QFam.exists_sz_scale | (intros; apply GlobalTheory.QFam.exists_sz_scale <;> assumption)
