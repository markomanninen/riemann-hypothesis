module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilCriterionInvariantMeasureHomogeneousSpace
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre

@[expose] public section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_criterion_invariant_measure_homogeneous_space : ModulusClause := by
  first | exact @GlobalTheory.WeilCriterion.modulusClause | exact GlobalTheory.WeilCriterion.modulusClause | (intros; apply GlobalTheory.WeilCriterion.modulusClause <;> assumption)
