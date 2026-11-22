module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSegmentRepresentation
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL in
theorem PositivityTheory.Exh.lSegExists (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    Zc.LSegExists k := fun Δ => GlobalTheory.CompanionTheory.SegExists.exists_isLSeg PositivityTheory.Exh.irreducibleAdmissibleGL Δ
