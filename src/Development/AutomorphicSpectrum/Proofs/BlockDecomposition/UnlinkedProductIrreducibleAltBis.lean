module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LUnlinkedIrr
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lUnlinkedIrr_of_irreducibleAdmissible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → GlobalTheory.Published.GeometricLemmaFiltration → GlobalTheory.BZSeg.NuPair k → GlobalTheory.BZSeg.WhitRankStd k → GlobalTheory.BZSeg.ProdIrrFiniteLength k → GlobalTheory.BZSeg.LUnlinkedIrr k := by
  first | exact @GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr | exact GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr | (intros; apply GlobalTheory.CompanionTheory.BZSeg.NuPairIrr.lUnlinkedIrr <;> assumption)
