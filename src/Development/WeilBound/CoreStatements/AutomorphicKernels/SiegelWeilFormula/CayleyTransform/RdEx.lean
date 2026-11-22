module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.FrameOfSig
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota

@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.Krd

theorem rdEx : RDEx := rdEx_of epsEx frEx iotaEx

end PositivityTheory.SiegelWeilFormula.Krd
