module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetRationalProductOfLocalLevels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_doubleCoset_rational_productOfLocalLevels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n)))) := by
  first | exact @GlobalTheory.BCT.finite_doubleCoset_globLev | exact GlobalTheory.BCT.finite_doubleCoset_globLev | (intros; apply GlobalTheory.BCT.finite_doubleCoset_globLev <;> assumption)
