module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentGenericOfJacquetNuPair
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_generic_of_jacquet_nu_pair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → GlobalTheory.BZSeg.NuPair k → GlobalTheory.BZSeg.LSegGeneric k := by
  first | exact @GlobalTheory.CompanionTheory.SegGenNu.lSegGeneric_of_nuPair | exact GlobalTheory.CompanionTheory.SegGenNu.lSegGeneric_of_nuPair | (intros; apply GlobalTheory.CompanionTheory.SegGenNu.lSegGeneric_of_nuPair <;> assumption)
