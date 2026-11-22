module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankStandardOfHeredity
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_rank_standard_of_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.WhitRankStd k := by
  first | exact @GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity | exact GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity | (intros; apply GlobalTheory.CompanionTheory.BZSeg.whitRankStd_of_heredity <;> assumption)
