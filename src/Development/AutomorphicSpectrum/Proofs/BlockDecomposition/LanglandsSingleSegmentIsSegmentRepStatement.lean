module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSingleSegmentIsSegmentRep
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_single_segment_is_segment_rep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsL {Δ} π → IsLSeg Δ π := by
  first | exact @GlobalTheory.CompanionTheory.LocGL.isLSeg_of_isL_singleton | exact GlobalTheory.CompanionTheory.LocGL.isLSeg_of_isL_singleton | (intros; apply GlobalTheory.CompanionTheory.LocGL.isLSeg_of_isL_singleton <;> assumption)
