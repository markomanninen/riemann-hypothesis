module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaCellSemisimplificationGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricLemma_cell_semisimplification_GL : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.CellSemisimplification k := by
  first | exact @GlobalTheory.SmGL.CellSemis.cellSemisimplification | exact GlobalTheory.SmGL.CellSemis.cellSemisimplification | (intros; apply GlobalTheory.SmGL.CellSemis.cellSemisimplification <;> assumption)
