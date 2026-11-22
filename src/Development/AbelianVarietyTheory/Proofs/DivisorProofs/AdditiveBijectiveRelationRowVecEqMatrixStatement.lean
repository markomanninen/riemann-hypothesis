module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveBijectiveRelationRowVecEqMatrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_bijective_relation_rowVec_eq_matrix : ∀ (N : ℕ) [NeZero N] (R : (Fin 2 → ZMod N) → (Fin 2 → ZMod N) → Prop), (∀ x, ∃ y, R x y) → (∀ x y x' y', R x y → R x' y' → R (x - x') (y - y')) → (∀ x y, R x y → (x = 0 ↔ y = 0)) → ∃ A : GL (Fin 2) (ZMod N), ∀ x, R x (vmul x A) := by
  first | exact @GlobalTheory.RelLin.main | exact GlobalTheory.RelLin.main | (intros; apply GlobalTheory.RelLin.main <;> assumption)
