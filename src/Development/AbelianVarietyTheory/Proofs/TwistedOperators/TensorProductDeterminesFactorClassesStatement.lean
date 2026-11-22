module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorProductDeterminesFactorClasses
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep

@[expose] public section

open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_product_determines_factor_classes : ∀ (β : Type) [Fintype β] (Γ : β → Type) [∀ j, Group (Γ j)] [∀ j, TopologicalSpace (Γ j)] (s s' : ∀ j, GlobalTheory.SmGL.IrrRep (Γ j)), Nonempty ((GlobalTheory.SmGL.piTensor fun j => (s j).ρ).Equiv (GlobalTheory.SmGL.piTensor fun j => (s' j).ρ)) → ∀ j, (s j).cl = (s' j).cl := by
  first | exact @GlobalTheory.TensorFactorUnique.cl_eq_of_piTensor_equiv | exact GlobalTheory.TensorFactorUnique.cl_eq_of_piTensor_equiv | (intros; apply GlobalTheory.TensorFactorUnique.cl_eq_of_piTensor_equiv <;> assumption)
