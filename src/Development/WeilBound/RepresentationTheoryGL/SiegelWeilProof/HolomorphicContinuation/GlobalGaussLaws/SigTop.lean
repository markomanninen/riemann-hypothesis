module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SigOKOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WittLt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WittEq

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem sigOK : SigOK := sigOK_of wittLBlt wittLBeq

end PositivityTheory.Rg.Sw.Glob
