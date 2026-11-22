module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.ScalarEx

theorem exists_scalarBy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (t : kˣ), ∃ c : ℂ, Zl.ScalarBy x t c := by
  intro k _ _ _ _ x t
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar x.2.rep.smooth x.2.rep.irr
  exact ⟨(ω t : ℂ), fun v => hω t v⟩

end GlobalTheory.CompanionTheory.ScalarEx
