module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjective
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_twist_injective : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (hx : x.IsCusp) (a b : ℕ) (h : x.nu (a : ℂ) = x.nu (b : ℂ)), a = b := by
  first | exact @GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj | exact GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj | (intros; apply GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj <;> assumption)
