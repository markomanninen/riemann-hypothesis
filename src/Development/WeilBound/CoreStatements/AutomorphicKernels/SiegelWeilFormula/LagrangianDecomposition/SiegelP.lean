module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Siegel
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DiagonalColumns.AdChar

@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem siegelSmall_of_slice (hF : SliceFacts) : SiegelSmall := siegelSmall_of hF Ldx.adaptedChar

end PositivityTheory.SiegelWeilFormula.Ald
