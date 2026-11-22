module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesAndDerivUniqueOfCoefficients
public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalSeriesAndDeriv_unique_of_coefficients : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (c : ℤ → Ω) (x x' y y' : Ω), Ev ψ c x x' → Ev ψ c y y' → x = y ∧ x' = y' := by
  first | exact @GlobalTheory.EvUniq.ev_unique | exact GlobalTheory.EvUniq.ev_unique | (intros; apply GlobalTheory.EvUniq.ev_unique <;> assumption)
