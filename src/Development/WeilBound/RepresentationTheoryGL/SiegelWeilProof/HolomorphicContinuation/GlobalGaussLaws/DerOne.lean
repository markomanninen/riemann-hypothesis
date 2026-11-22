module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOneB
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOneC

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem derivOne (h : GlobalTheory.Published.WeilThetaConvergence) : DerivOne := derivOne_of h curveSt

end PositivityTheory.Rg.Sw.Glob
