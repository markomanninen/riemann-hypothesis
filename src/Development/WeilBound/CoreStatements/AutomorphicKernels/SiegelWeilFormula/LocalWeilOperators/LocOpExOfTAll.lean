module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Assemble
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.WeylElementTransposeMul

@[expose] public section

namespace PositivityTheory.SiegelWeilFormula

theorem locOpEx_of_tAll (hT : TAll) : LocOpEx := locOpEx_of hT kfour.auxEx

end PositivityTheory.SiegelWeilFormula
