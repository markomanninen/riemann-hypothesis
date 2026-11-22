module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassTorsionQExpansionIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassTorsion_qExpansion_integral : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N), ¬ l ∣ M → M • x = 0 → x ≠ 0 → QAll (Sz l lam 0) N (wB N x) ∧ QAll (Sz l lam 0) N (wpd N x) := by
  first | exact @GlobalTheory.WpFam.ExpansionIntegral.main | exact GlobalTheory.WpFam.ExpansionIntegral.main | (intros; apply GlobalTheory.WpFam.ExpansionIntegral.main <;> assumption)
