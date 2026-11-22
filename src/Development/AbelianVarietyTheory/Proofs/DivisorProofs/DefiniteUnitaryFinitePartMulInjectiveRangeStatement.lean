module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryFinitePart_mul_injective_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ a b : UE E n, finPt (a * b) = finPt a * finPt b) ∧ Function.Injective (finPt : UE E n → finU (E := E) (n := n)) ∧ ∀ x : finU (E := E) (n := n), x ∈ ratFinU E n ↔ ∃ γ : UE E n, finPt γ = x := by
  first | exact @GlobalTheory.BCT.FinPart.finPt_props | exact GlobalTheory.BCT.FinPart.finPt_props | (intros; apply GlobalTheory.BCT.FinPart.finPt_props <;> assumption)
