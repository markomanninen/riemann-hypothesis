module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.PartCharInvOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SplitPoint

@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem partCharInv : PartCharInv := PCI.partCharInv_of PCI.finPart

end PositivityTheory.SiegelWeilFormula.Ald
