module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.InducedCellSemisimplification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_cell_semisimplification : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.CellSemisimplification k := by
  first | exact @GlobalTheory.CompanionTheory.Glob.cellSemisimplification | exact GlobalTheory.CompanionTheory.Glob.cellSemisimplification | (intros; apply GlobalTheory.CompanionTheory.Glob.cellSemisimplification <;> assumption)
