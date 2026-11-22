module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylRowActionMemWeylLatticeSquare
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylRowAction_mem_weylLattice_square : ∀ (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ (M : Matrix (Fin n) (Fin n) R), ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν, Formalism.GradedWeylDivisibility.rowAct R M f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν := by
  first | exact @GlobalTheory.WeylRowAll.rowAct_mem_weyl_square | exact GlobalTheory.WeylRowAll.rowAct_mem_weyl_square | (intros; apply GlobalTheory.WeylRowAll.rowAct_mem_weyl_square <;> assumption)
