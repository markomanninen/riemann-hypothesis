module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteUnitaryRationalOfIsOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPtHomApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_doubleCoset_definiteUnitaryRational_of_isOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (L : Subgroup (finU (E := E) (n := n))), IsOpen (L : Set (finU (E := E) (n := n))) → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (L : Set (finU (E := E) (n := n)))) := by
  first | exact @GlobalTheory.BCT.finite_doubleCoset_ratFinU_isOpen | exact GlobalTheory.BCT.finite_doubleCoset_ratFinU_isOpen | (intros; apply GlobalTheory.BCT.finite_doubleCoset_ratFinU_isOpen <;> assumption)
