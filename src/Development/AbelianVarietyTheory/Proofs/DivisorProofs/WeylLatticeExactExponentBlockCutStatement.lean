module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylLatticeExactExponentBlockCut
public import Formalism.PieriBlockIdeals.StatementE
public import Formalism.PieriBlockIdeals.TailInequalityEventually

@[expose] public section

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylLattice_exact_exponent_block_cut : Formalism.CohomologicalDescent.E.ExCut := by
  first | exact @GlobalTheory.LeviCut.exCut | exact GlobalTheory.LeviCut.exCut | (intros; apply GlobalTheory.LeviCut.exCut <;> assumption)
