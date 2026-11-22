module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOfExpansionSumEqPrimePowMulIsEval
public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_expansionSum_eq_primePow_mul_isEval : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p), (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp p (e t)) → ∀ (v : ℕ) (o : Ω), IsInt (p := p) o → ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) = (p : Ω) ^ v * o → ∃ (c : ℤ → Ω) (x' : Ω), Ev ψ c o x' := by
  first | exact @GlobalTheory.GeoFix.Divide.divide_ev | exact GlobalTheory.GeoFix.Divide.divide_ev | (intros; apply GlobalTheory.GeoFix.Divide.divide_ev <;> assumption)
