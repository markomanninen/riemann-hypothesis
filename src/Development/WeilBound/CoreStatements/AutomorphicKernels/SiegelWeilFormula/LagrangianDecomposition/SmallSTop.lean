module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallS
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.HaarLc

@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem smallS_of' : ChartFacts → SliceFacts → SmallS := fun hC hF => smallS_of hC hF (subSplit_of hF) haarLc

end PositivityTheory.SiegelWeilFormula.Ald
