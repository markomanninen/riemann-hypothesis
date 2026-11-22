module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompactSubgroupQuotientInvariantMeasure
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre

@[expose] public section

open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactSubgroup_quotient_invariant_measure : CompactClause := by
  first | exact @GlobalTheory.QuotientMeasureCompact.compactClause | exact GlobalTheory.QuotientMeasureCompact.compactClause | (intros; apply GlobalTheory.QuotientMeasureCompact.compactClause <;> assumption)
